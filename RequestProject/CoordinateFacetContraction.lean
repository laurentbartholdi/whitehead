module

public import RequestProject.QCubeCoordinateEquiv
public import RequestProject.OrderCxNullTransfer

@[expose] public section

/-! Coordinate maps used to contract a cube boundary after deletion of one facet. -/
namespace FiniteChains.Davis
variable {V : Type} [DecidableEq V]

def coordinateFix (j : V) (z : CubeCoord) (c : Cube V) : Cube V :=
  Function.update c j z

/-- Open the selected coordinate, except on the opposite facet, which stays fixed. -/
def coordinateOpen (j : V) (z : CubeCoord) (c : Cube V) : Cube V :=
  if c j = z then c else Function.update c j CubeCoord.free

theorem coordinateFix_face_mono (j : V) (z : CubeCoord) {c d : Cube V}
    (h : CoordinateFace c d) : CoordinateFace (coordinateFix j z c) (coordinateFix j z d) := by
  intro v
  by_cases hv : v = j
  · subst v
    right
    simp only [coordinateFix, Function.update_self]
  · simpa only [coordinateFix, Function.update_of_ne hv] using h v

theorem coordinateOpen_face_mono (j : V) (z : CubeCoord) (hz : z ≠ CubeCoord.free)
    {c d : Cube V} (h : CoordinateFace c d) :
    CoordinateFace (coordinateOpen j z c) (coordinateOpen j z d) := by
  intro v
  by_cases hv : v = j
  · subst v
    by_cases hd : d j = z
    · have hc : c j = z := by
        rcases h j with hf | he
        · exact False.elim (hz (hd.symm.trans hf))
        · exact he.trans hd
      right
      simp [coordinateOpen, hc, hd]
    · left
      simp only [coordinateOpen, if_neg hd, Function.update_self]
  · have hc : coordinateOpen j z c v = c v := by
      unfold coordinateOpen
      split
      · rfl
      · exact Function.update_of_ne hv _ _
    have hd : coordinateOpen j z d v = d v := by
      unfold coordinateOpen
      split
      · rfl
      · exact Function.update_of_ne hv _ _
    rw [hc, hd]
    exact h v

theorem coordinate_face_open (j : V) (z : CubeCoord) (c : Cube V) :
    CoordinateFace c (coordinateOpen j z c) := by
  intro v
  unfold coordinateOpen
  split
  · exact Or.inr rfl
  · by_cases hv : v = j
    · subst v
      exact Or.inl (Function.update_self _ _ _)
    · right
      rw [Function.update_of_ne hv]

theorem coordinate_fix_face_open (j : V) (z : CubeCoord) (c : Cube V) :
    CoordinateFace (coordinateFix j z c) (coordinateOpen j z c) := by
  intro v
  by_cases hv : v = j
  · subst v
    by_cases hc : c j = z
    · right
      simp [coordinateFix, coordinateOpen, hc, Function.update_self]
    · left
      simp only [coordinateOpen, if_neg hc, Function.update_self]
  · have ho : coordinateOpen j z c v = c v := by
      unfold coordinateOpen
      split
      · rfl
      · exact Function.update_of_ne hv _ _
    right
    simp only [coordinateFix, Function.update_of_ne hv, ho]

theorem coordinateFix_face_opposite_facet (j : V) (z : CubeCoord)
    {c t : Cube V} (h : CoordinateFace c t) :
    CoordinateFace (coordinateFix j z c) (coordinateFix j z t) :=
  coordinateFix_face_mono j z h

theorem coordinateOpen_face_top (j : V) (z : CubeCoord)
    {c t : Cube V} (ht : t j = CubeCoord.free) (h : CoordinateFace c t) :
    CoordinateFace (coordinateOpen j z c) t := by
  intro v
  by_cases hv : v = j
  · subst v
    exact Or.inl ht
  · have ho : coordinateOpen j z c v = c v := by
      unfold coordinateOpen
      split
      · rfl
      · exact Function.update_of_ne hv _ _
    rw [ho]
    exact h v

theorem cubeCoord_cases_of_opposite (b z : CubeCoord) (hb : b ≠ CubeCoord.free)
    (hz : z ≠ CubeCoord.free) (hbz : b ≠ z) (s : CubeCoord) :
    s = CubeCoord.free ∨ s = b ∨ s = z := by
  cases b <;> cases z <;> cases s <;> simp_all

theorem coordinateOpen_ne_top (j : V) (b z : CubeCoord)
    (hb : b ≠ CubeCoord.free) (hz : z ≠ CubeCoord.free) (hbz : b ≠ z)
    {c t : Cube V} (ht : t j = CubeCoord.free) (hct : c ≠ t)
    (hcf : c ≠ coordinateFix j b t) : coordinateOpen j z c ≠ t := by
  intro he
  by_cases hc : c j = z
  · exact hct (by simpa [coordinateOpen, hc] using he)
  · have hrest : ∀ v, v ≠ j → c v = t v := by
      intro v hv
      have hh := congrFun he v
      simpa only [coordinateOpen, if_neg hc, Function.update_of_ne hv] using hh
    rcases cubeCoord_cases_of_opposite b z hb hz hbz (c j) with hfree | hval | hval
    · apply hct
      funext v
      by_cases hv : v = j
      · subst v
        exact hfree.trans ht.symm
      · exact hrest v hv
    · apply hcf
      funext v
      by_cases hv : v = j
      · subst v
        simpa only [coordinateFix, Function.update_self] using hval
      · simpa only [coordinateFix, Function.update_of_ne hv] using hrest v hv
    · exact hc hval

theorem coordinateFix_ne_top (j : V) (z : CubeCoord) (hz : z ≠ CubeCoord.free)
    {c t : Cube V} (ht : t j = CubeCoord.free) : coordinateFix j z c ≠ t := by
  intro he
  have hh := congrFun he j
  simp only [coordinateFix, Function.update_self, ht] at hh
  exact hz hh

theorem coordinateFix_ne_facet (j : V) (b z : CubeCoord) (hbz : b ≠ z)
    (c t : Cube V) : coordinateFix j z c ≠ coordinateFix j b t := by
  intro he
  have hh := congrFun he j
  simp only [coordinateFix, Function.update_self] at hh
  exact hbz hh.symm

theorem coordinateOpen_ne_facet (j : V) (b z : CubeCoord)
    (hb : b ≠ CubeCoord.free) (hbz : b ≠ z) (c t : Cube V) :
    coordinateOpen j z c ≠ coordinateFix j b t := by
  intro he
  have hh := congrFun he j
  by_cases hc : c j = z
  · simp only [coordinateOpen, if_pos hc, coordinateFix, Function.update_self] at hh
    exact hbz (hh.symm.trans hc)
  · simp only [coordinateOpen, if_neg hc, coordinateFix, Function.update_self] at hh
    exact hb hh.symm

end FiniteChains.Davis
