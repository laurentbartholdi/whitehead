import RequestProject.ChamberQuotient
import RequestProject.TruncatedCube
import RequestProject.CmpNerve

/-! The quotient cube cells are the actual coordinate cubes used in the geometric collapse. -/

namespace FiniteChains.Davis
open RACG Mirror
variable {V : Type} [DecidableEq V] [Fintype V] {A : CommRel V}

/-- Zero parity is the positive corner, consistently with the corner removed in `QOld`. -/
def qCubeToCoordinate (c : QCube A) : Cube V := fun v =>
  if v ∈ c.spx then CubeCoord.free else if c.sgn v = 0 then CubeCoord.pos else CubeCoord.neg

@[simp] theorem freeSet_qCubeToCoordinate (c : QCube A) :
    freeSet (qCubeToCoordinate c) = c.spx := by
  ext v
  by_cases hv : v ∈ c.spx <;> by_cases hs : c.sgn v = 0 <;>
    simp [qCubeToCoordinate, hv, hs]

/-- The same admissible cells as the cube-poset quotient, expressed in coordinates. -/
def CoordinateCube (A : CommRel V) := {c : Cube V // IsSimplex A (freeSet c)}

def coordinateToQCube (c : CoordinateCube A) : QCube A where
  spx := freeSet c.1
  sgn v := match c.1 v with
    | CubeCoord.neg => 1
    | _ => 0
  isSimplex := c.2
  sgn_eq_zero v hv := by
    rw [mem_freeSet] at hv
    simp [hv]

@[simp] theorem coordinateToQCube_toCoordinate (c : CoordinateCube A) :
    qCubeToCoordinate (coordinateToQCube c) = c.1 := by
  funext v
  cases h : c.1 v <;> simp [qCubeToCoordinate, coordinateToQCube, mem_freeSet, h]

/-- The coordinate identification is an actual equivalence of cell sets. -/
def qCubeCoordinateEquiv : QCube A ≃ CoordinateCube A where
  toFun c := ⟨qCubeToCoordinate c, by simpa using c.isSimplex⟩
  invFun := coordinateToQCube
  left_inv c := by
    apply QCube.ext'
    · exact freeSet_qCubeToCoordinate c
    · intro v hv
      change (match qCubeToCoordinate c v with | CubeCoord.neg => 1 | _ => 0) = c.sgn v
      have hz : c.sgn v = 0 ∨ c.sgn v = 1 := by
        generalize c.sgn v = z
        revert z
        decide
      rcases hz with hz | hz <;> simp [qCubeToCoordinate, hv, hz]
  right_inv c := Subtype.ext (coordinateToQCube_toCoordinate c)

omit [Fintype V] in
/-- The positive corner cubes of the quotient are precisely the cubes meeting the cut. -/
theorem qCubeToCoordinate_sgn_zero (c : QCube A) (hc : c.sgn = 0) :
    qCubeToCoordinate c = posCube c.spx := by
  funext v
  simp [qCubeToCoordinate, posCube, hc]

/-- Recover the parity sign from the actual fixed coordinate. -/
theorem qCubeToCoordinate_parity (c : QCube A) (v : V) :
    (match qCubeToCoordinate c v with | CubeCoord.neg => (1 : ZMod 2) | _ => 0) =
      c.sgn v := by
  exact congrArg (fun d : QCube A => d.sgn v) (qCubeCoordinateEquiv.left_inv c)

/-- A coordinate cube is a face of another when each coordinate of the larger cube is
 free or agrees with the smaller cube. -/
def CoordinateFace (c d : Cube V) : Prop := ∀ v, d v = CubeCoord.free ∨ c v = d v

/-- The poset used in the full Davis nerve is exactly the coordinate-cube face poset. -/
theorem qCubeToCoordinate_face_iff (c d : QCube A) :
    c ≤ d ↔ CoordinateFace (qCubeToCoordinate c) (qCubeToCoordinate d) := by
  constructor
  · intro h v
    by_cases hv : v ∈ d.spx
    · exact Or.inl (by simp [qCubeToCoordinate, hv])
    · right
      have hvc : v ∉ c.spx := fun hc => hv (h.1 hc)
      simp [qCubeToCoordinate, hv, hvc, h.2 v hv]
  · intro h
    refine ⟨?_, ?_⟩
    · intro v hv
      have hc : qCubeToCoordinate c v = CubeCoord.free := by
        simp [qCubeToCoordinate, hv]
      have hd : qCubeToCoordinate d v = CubeCoord.free := by
        rcases h v with hd | hd
        · exact hd
        · exact hd.symm.trans hc
      have hm : v ∈ freeSet (qCubeToCoordinate d) := mem_freeSet.mpr hd
      simpa using hm
    · intro v hv
      have hd : qCubeToCoordinate d v ≠ CubeCoord.free := by
        intro he
        have hm := mem_freeSet.mpr he
        rw [freeSet_qCubeToCoordinate] at hm
        exact hv hm
      have he : qCubeToCoordinate c v = qCubeToCoordinate d v := (h v).resolve_left hd
      rw [← qCubeToCoordinate_parity c v, ← qCubeToCoordinate_parity d v, he]

instance : PartialOrder (CoordinateCube A) where
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

/-- The identification preserves all face incidences, not just the sets of cells. -/
def qCubeCoordinateOrderIso : QCube A ≃o CoordinateCube A where
  toEquiv := qCubeCoordinateEquiv
  map_rel_iff' := by
    intro c d
    exact (qCubeToCoordinate_face_iff c d).symm

/-- The excluded quotient vertex is exactly the constant positive coordinate cube. -/
theorem qCubeToCoordinate_eq_positive_iff (c : QCube A) :
    qCubeToCoordinate c = (fun _ => CubeCoord.pos) ↔ c.spx = ∅ ∧ c.sgn = 0 := by
  constructor
  · intro h
    constructor
    · rw [← freeSet_qCubeToCoordinate, h]
      ext v
      simp [mem_freeSet]
    · funext v
      rw [← qCubeToCoordinate_parity, h]
      rfl
  · rintro ⟨hs, hg⟩
    funext v
    simp [qCubeToCoordinate, hs, hg]

/-- The old cells exclude precisely the removed positive vertex. This does not include
the new cut faces of the truncated complex. -/
def qOldCoordinateEquiv : QOld A ≃
    {c : CoordinateCube A // c.1 ≠ (fun _ => CubeCoord.pos)} where
  toFun c := ⟨qCubeCoordinateEquiv c.1, fun h =>
    c.2 ((qCubeToCoordinate_eq_positive_iff c.1).mp h)⟩
  invFun c := ⟨coordinateToQCube c.1, fun h => c.2 (by
    rw [← coordinateToQCube_toCoordinate c.1]
    exact (qCubeToCoordinate_eq_positive_iff _).mpr h)⟩
  left_inv c := Subtype.ext (qCubeCoordinateEquiv.left_inv c.1)
  right_inv c := Subtype.ext (qCubeCoordinateEquiv.right_inv c.1)

end FiniteChains.Davis

namespace FiniteChains.Davis

open RACG Mirror

variable {P : Type} [PartialOrder P] [DecidableEq P] [Fintype P]

/-- For a comparability nerve, admissibility is exactly the moment-angle cell condition
used by the geometric collapse. -/
theorem coordinateCube_cmpRel_iff (c : Cube P) :
    IsSimplex (cmpRel P) (freeSet c) ↔ InMA (ASC.orderComplex P) c := by
  rw [isSimplex_cmpRel_iff]
  constructor
  · intro h x hx y hy _
    exact h x hx y hy
  · intro h x hx y hy
    by_cases he : x = y
    · exact Or.inl (le_of_eq he)
    · exact h hx hy he

/-- The quotient cubes and the moment-angle cubes have the same actual coordinates. -/
def qCubeMomentAngleEquiv : QCube (cmpRel P) ≃
    {c : Cube P // InMA (ASC.orderComplex P) c} :=
  qCubeCoordinateEquiv.trans
    { toFun := fun c => ⟨c.1, (coordinateCube_cmpRel_iff c.1).mp c.2⟩
      invFun := fun c => ⟨c.1, (coordinateCube_cmpRel_iff c.1).mpr c.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end FiniteChains.Davis
