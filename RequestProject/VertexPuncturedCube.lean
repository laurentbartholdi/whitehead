import RequestProject.CoordinateFacetContraction

/-! Coordinate regions of the proper three-cube boundary with its positive vertex removed. -/
namespace FiniteChains.Davis
open Comb

def VertexPuncturedCube :=
  {c : Cube (Fin 3) // c ≠ (fun _ => CubeCoord.free) ∧ c ≠ (fun _ => CubeCoord.pos)}

instance : PartialOrder VertexPuncturedCube where
  le c d := CoordinateFace c.1 d.1
  le_refl c v := Or.inr rfl
  le_trans c d e hcd hde v := by
    rcases hde v with he | he
    · exact Or.inl he
    · rcases hcd v with hd | hd
      · exact Or.inl (he.symm.trans hd)
      · exact Or.inr (hd.trans he)
  le_antisymm c d hcd hdc := by
    apply Subtype.ext
    funext v
    rcases hcd v with hd | hd
    · rcases hdc v with hc | hc
      · exact hc.trans hd.symm
      · exact hc.symm
    · exact hd

def vertexPunctureRight (c : VertexPuncturedCube) : Prop := c.1 0 ≠ CubeCoord.pos

def vertexPunctureRightPole : {c : VertexPuncturedCube // vertexPunctureRight c} :=
  ⟨⟨coordinateFix 0 CubeCoord.neg (fun _ => CubeCoord.free), by
      constructor
      · intro h
        have hh := congrFun h 0
        simp only [coordinateFix, Function.update_self] at hh
        cases hh
      · intro h
        have hh := congrFun h 0
        simp only [coordinateFix, Function.update_self] at hh
        cases hh⟩, by
    change coordinateFix 0 CubeCoord.neg (fun _ : Fin 3 => CubeCoord.free) 0 ≠ CubeCoord.pos
    simp only [coordinateFix, Function.update_self]
    decide⟩

def vertexPunctureRightProjection (c : {c : VertexPuncturedCube // vertexPunctureRight c}) :
    {c : VertexPuncturedCube // vertexPunctureRight c} :=
  ⟨⟨coordinateFix 0 CubeCoord.neg c.1.1, by
      constructor
      · intro h
        have hh := congrFun h 0
        simp only [coordinateFix, Function.update_self] at hh
        cases hh
      · intro h
        have hh := congrFun h 0
        simp only [coordinateFix, Function.update_self] at hh
        cases hh⟩, by
    change coordinateFix 0 CubeCoord.neg c.1.1 0 ≠ CubeCoord.pos
    simp only [coordinateFix, Function.update_self]
    decide⟩

theorem vertexPunctureRightProjection_le
    (c : {c : VertexPuncturedCube // vertexPunctureRight c}) :
    vertexPunctureRightProjection c ≤ c := by
  intro v
  by_cases hv : v = 0
  · subst v
    have hc : c.1.1 0 ≠ CubeCoord.pos := c.2
    cases he : c.1.1 0 with
    | free => exact Or.inl rfl
    | pos => exact False.elim (hc he)
    | neg =>
      right
      simp only [vertexPunctureRightProjection, coordinateFix, Function.update_self]
  · right
    exact Function.update_of_ne hv _ _

theorem vertexPunctureRightProjection_le_pole
    (c : {c : VertexPuncturedCube // vertexPunctureRight c}) :
    vertexPunctureRightProjection c ≤ vertexPunctureRightPole :=
  coordinateFix_face_mono 0 CubeCoord.neg (fun _ => Or.inl rfl)

theorem vertexPunctureRightProjection_monotone : Monotone vertexPunctureRightProjection := by
  intro c d h
  exact coordinateFix_face_mono 0 CubeCoord.neg h

theorem vertexPunctureRight_simplyConnected :
    SimplyConnected (orderCx {c : VertexPuncturedCube // vertexPunctureRight c}) :=
  simplyConnected_orderCx vertexPunctureRightPole vertexPunctureRightProjection
    vertexPunctureRightProjection_le vertexPunctureRightProjection_le_pole
    (fun h => vertexPunctureRightProjection_monotone h)

theorem vertexPunctureRight_connected :
    IsConnected (orderCx {c : VertexPuncturedCube // vertexPunctureRight c}) :=
  isConnected_orderCx vertexPunctureRightPole vertexPunctureRightProjection
    vertexPunctureRightProjection_le vertexPunctureRightProjection_le_pole

def vertexPunctureCornerEdge : Cube (Fin 3) := coordinateFix 0 CubeCoord.free (fun _ => CubeCoord.pos)

def vertexPunctureLeft (c : VertexPuncturedCube) : Prop :=
  c.1 0 ≠ CubeCoord.neg ∧ c.1 ≠ vertexPunctureCornerEdge

theorem vertexPunctureLeftProjection_ne_vertex
    (c : {c : VertexPuncturedCube // vertexPunctureLeft c}) :
    coordinateFix 0 CubeCoord.pos c.1.1 ≠ (fun _ => CubeCoord.pos) := by
  intro h
  have hrest (v : Fin 3) (hv : v ≠ 0) : c.1.1 v = CubeCoord.pos := by
    have hh := congrFun h v
    simpa only [coordinateFix, Function.update_of_ne hv] using hh
  cases he : c.1.1 0 with
  | neg => exact c.2.1 he
  | pos =>
    apply c.1.2.2
    funext v
    by_cases hv : v = 0
    · subst v
      exact he
    · exact hrest v hv
  | free =>
    apply c.2.2
    funext v
    by_cases hv : v = 0
    · subst v
      simpa only [vertexPunctureCornerEdge, coordinateFix, Function.update_self] using he
    · simpa only [vertexPunctureCornerEdge, coordinateFix, Function.update_of_ne hv] using hrest v hv

def vertexPunctureLeftPole : {c : VertexPuncturedCube // vertexPunctureLeft c} :=
  ⟨⟨coordinateFix 0 CubeCoord.pos (fun _ => CubeCoord.free), by
      constructor
      · intro h
        have hh := congrFun h 0
        simp only [coordinateFix, Function.update_self] at hh
        cases hh
      · intro h
        have hh := congrFun h (1 : Fin 3)
        simp only [coordinateFix, Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0)] at hh
        cases hh⟩, by
    constructor
    · change coordinateFix 0 CubeCoord.pos (fun _ : Fin 3 => CubeCoord.free) 0 ≠ CubeCoord.neg
      simp only [coordinateFix, Function.update_self]
      decide
    · intro h
      have hh := congrFun h 0
      simp only [vertexPunctureCornerEdge, coordinateFix, Function.update_self] at hh
      cases hh⟩

def vertexPunctureLeftProjection (c : {c : VertexPuncturedCube // vertexPunctureLeft c}) :
    {c : VertexPuncturedCube // vertexPunctureLeft c} :=
  ⟨⟨coordinateFix 0 CubeCoord.pos c.1.1, by
      constructor
      · intro h
        have hh := congrFun h 0
        simp only [coordinateFix, Function.update_self] at hh
        cases hh
      · exact vertexPunctureLeftProjection_ne_vertex c⟩, by
    constructor
    · change coordinateFix 0 CubeCoord.pos c.1.1 0 ≠ CubeCoord.neg
      simp only [coordinateFix, Function.update_self]
      decide
    · intro h
      have hh := congrFun h 0
      simp only [vertexPunctureCornerEdge, coordinateFix, Function.update_self] at hh
      cases hh⟩

theorem vertexPunctureLeftProjection_le
    (c : {c : VertexPuncturedCube // vertexPunctureLeft c}) :
    vertexPunctureLeftProjection c ≤ c := by
  intro v
  by_cases hv : v = 0
  · subst v
    cases he : c.1.1 0 with
    | free => exact Or.inl rfl
    | neg => exact False.elim (c.2.1 he)
    | pos =>
      right
      simp only [vertexPunctureLeftProjection, coordinateFix, Function.update_self]
  · right
    exact Function.update_of_ne hv _ _

theorem vertexPunctureLeftProjection_le_pole
    (c : {c : VertexPuncturedCube // vertexPunctureLeft c}) :
    vertexPunctureLeftProjection c ≤ vertexPunctureLeftPole :=
  coordinateFix_face_mono 0 CubeCoord.pos (fun _ => Or.inl rfl)

theorem vertexPunctureLeftProjection_monotone : Monotone vertexPunctureLeftProjection := by
  intro c d h
  exact coordinateFix_face_mono 0 CubeCoord.pos h

theorem vertexPunctureLeft_simplyConnected :
    SimplyConnected (orderCx {c : VertexPuncturedCube // vertexPunctureLeft c}) :=
  simplyConnected_orderCx vertexPunctureLeftPole vertexPunctureLeftProjection
    vertexPunctureLeftProjection_le vertexPunctureLeftProjection_le_pole
    (fun h => vertexPunctureLeftProjection_monotone h)

theorem vertexPunctureLeft_connected :
    IsConnected (orderCx {c : VertexPuncturedCube // vertexPunctureLeft c}) :=
  isConnected_orderCx vertexPunctureLeftPole vertexPunctureLeftProjection
    vertexPunctureLeftProjection_le vertexPunctureLeftProjection_le_pole

theorem vertexPuncture_positive_mem_left (c : VertexPuncturedCube)
    (hc : c.1 0 = CubeCoord.pos) : vertexPunctureLeft c := by
  constructor
  · rw [hc]
    decide
  · intro h
    have hh := congrFun h 0
    simp only [vertexPunctureCornerEdge, coordinateFix, Function.update_self, hc] at hh
    cases hh

theorem vertexPuncture_cover (c : VertexPuncturedCube) :
    vertexPunctureLeft c ∨ vertexPunctureRight c := by
  by_cases hc : c.1 0 = CubeCoord.pos
  · exact Or.inl (vertexPuncture_positive_mem_left c hc)
  · exact Or.inr hc

theorem vertexPuncture_positive_not_below_edge (c : VertexPuncturedCube)
    (hc : c.1 0 = CubeCoord.pos) : ¬ CoordinateFace c.1 vertexPunctureCornerEdge := by
  intro h
  apply c.2.2
  funext v
  by_cases hv : v = 0
  · subst v
    exact hc
  · have he : vertexPunctureCornerEdge v = CubeCoord.pos := by
      simp only [vertexPunctureCornerEdge, coordinateFix, Function.update_of_ne hv]
    have hh := h v
    rw [he] at hh
    rcases hh with hh | hh
    · cases hh
    · exact hh

theorem vertexPuncture_unmixed (c d : VertexPuncturedCube) (h : c ≤ d) :
    (vertexPunctureLeft c ∧ vertexPunctureLeft d) ∨
      (vertexPunctureRight c ∧ vertexPunctureRight d) := by
  cases hd : d.1 0 with
  | pos =>
    have hc : c.1 0 = CubeCoord.pos := by
      have hh := h 0
      rw [hd] at hh
      rcases hh with hh | hh
      · cases hh
      · exact hh
    exact Or.inl ⟨vertexPuncture_positive_mem_left c hc, vertexPuncture_positive_mem_left d hd⟩
  | neg =>
    have hc : c.1 0 = CubeCoord.neg := by
      have hh := h 0
      rw [hd] at hh
      rcases hh with hh | hh
      · cases hh
      · exact hh
    right
    constructor <;> change _ ≠ CubeCoord.pos
    · rw [hc]
      decide
    · rw [hd]
      decide
  | free =>
    have hdr : vertexPunctureRight d := by
      change d.1 0 ≠ CubeCoord.pos
      rw [hd]
      decide
    by_cases hcr : vertexPunctureRight c
    · exact Or.inr ⟨hcr, hdr⟩
    · have hc : c.1 0 = CubeCoord.pos := not_ne_iff.mp hcr
      left
      refine ⟨vertexPuncture_positive_mem_left c hc, ?_⟩
      constructor
      · rw [hd]
        decide
      · intro he
        exact vertexPuncture_positive_not_below_edge c hc (he ▸ h)

theorem vertexPuncture_intersection_iff (c : VertexPuncturedCube) :
    vertexPunctureLeft c ∧ vertexPunctureRight c ↔
      c.1 0 = CubeCoord.free ∧ c.1 ≠ vertexPunctureCornerEdge := by
  constructor
  · rintro ⟨⟨hn, he⟩, hp⟩
    refine ⟨?_, he⟩
    cases hc : c.1 0 with
    | free => rfl
    | pos => exact False.elim (hp hc)
    | neg => exact False.elim (hn hc)
  · rintro ⟨hf, he⟩
    constructor
    · refine ⟨?_, he⟩
      rw [hf]
      decide
    · change c.1 0 ≠ CubeCoord.pos
      rw [hf]
      decide

end FiniteChains.Davis
