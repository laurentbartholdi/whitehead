import RequestProject.QCubeEdgeSubdivision

/-! Actual coordinate facets of quotient cubes. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def qCubeFacet (c : QCube A) (v : V) (s : ZMod 2) : QCube A where
  spx := c.spx.erase v
  sgn := Function.update c.sgn v s
  isSimplex := isSimplex_subset A (Finset.erase_subset _ _) c.isSimplex
  sgn_eq_zero w hw := by
    have h := Finset.mem_erase.mp hw
    rw [Function.update_of_ne h.1]
    exact c.sgn_eq_zero w h.2

theorem qCubeFacet_le (c : QCube A) (v : V) (s : ZMod 2) (hv : v ∈ c.spx) :
    qCubeFacet c v s ≤ c := by
  refine ⟨Finset.erase_subset _ _, ?_⟩
  intro w hw
  have hne : w ≠ v := fun h => hw (h.symm ▸ hv)
  exact Function.update_of_ne hne _ _

theorem qCubeFacet_lt (c : QCube A) (v : V) (s : ZMod 2) (hv : v ∈ c.spx) :
    qCubeFacet c v s < c := by
  apply lt_of_le_of_ne (qCubeFacet_le c v s hv)
  intro h
  have hs : c.spx.erase v = c.spx := congrArg QCube.spx h
  have hm : v ∈ c.spx.erase v := hs.symm ▸ hv
  exact (Finset.notMem_erase v c.spx) hm

@[simp] theorem qCubeFacet_sgn_self (c : QCube A) (v : V) (s : ZMod 2) :
    (qCubeFacet c v s).sgn v = s := Function.update_self _ _ _

/-- Fixing two distinct directions gives the same actual face in either order. -/
theorem qCubeFacet_comm (c : QCube A) {v w : V} (hne : v ≠ w) (s t : ZMod 2) :
    qCubeFacet (qCubeFacet c v s) w t = qCubeFacet (qCubeFacet c w t) v s := by
  apply QCube.ext'
  · change (c.spx.erase v).erase w = (c.spx.erase w).erase v
    ext x
    simp only [Finset.mem_erase]
    tauto
  · intro x _
    change Function.update (Function.update c.sgn v s) w t x =
      Function.update (Function.update c.sgn w t) v s x
    by_cases hxv : x = v
    · subst x
      simp [hne]
    · by_cases hxw : x = w
      · subst x
        simp [Ne.symm hne]
      · simp [hxv, hxw]

theorem qCubeFacet_zero_of_singleton (c : QCube A) (v : V) (hs : c.spx = {v}) :
    qCubeFacet c v 0 = cubePositiveVertex c := by
  apply QCube.ext'
  · simp [qCubeFacet, cubePositiveVertex, hs]
  · intro w _
    change Function.update c.sgn v 0 w = c.sgn w
    by_cases h : w = v
    · subst w
      rw [Function.update_self]
      exact (c.sgn_eq_zero v (by rw [hs]; simp)).symm
    · exact Function.update_of_ne h _ _

theorem qCubeFacet_one_of_singleton (c : QCube A) (v : V) (hs : c.spx = {v}) :
    qCubeFacet c v 1 = cubeNegativeVertex c v := by
  apply QCube.ext'
  · simp [qCubeFacet, cubeNegativeVertex, hs]
  · intro _ _
    rfl

/-- The strict one-cell subdivision agrees with the actual oriented cubical facets. -/
theorem oneCubeSubdivision_facet_boundary (c : QCube A) (v : V) (hs : c.spx = {v}) :
    Comb.bdry1 (strictOrderCx (QCube A)) (oneCubeSubdivision c v hs) =
      Finsupp.single (qCubeFacet c v 0) 1 - Finsupp.single (qCubeFacet c v 1) 1 := by
  rw [oneCubeSubdivision_boundary, qCubeFacet_zero_of_singleton c v hs,
    qCubeFacet_one_of_singleton c v hs]


/-- Positive facets are exactly the positive coordinate fixes used by the collapse. -/
theorem qCubeFacet_coordinate_zero (c : QCube A) (v : V) :
    qCubeToCoordinate (qCubeFacet c v 0) =
      Function.update (qCubeToCoordinate c) v CubeCoord.pos := by
  funext w
  by_cases h : w = v
  · subst w
    simp [qCubeToCoordinate, qCubeFacet]
  · simp [qCubeToCoordinate, qCubeFacet, h]

/-- Negative facets are exactly the negative coordinate fixes used by the collapse. -/
theorem qCubeFacet_coordinate_one (c : QCube A) (v : V) :
    qCubeToCoordinate (qCubeFacet c v 1) =
      Function.update (qCubeToCoordinate c) v CubeCoord.neg := by
  funext w
  by_cases h : w = v
  · subst w
    simp [qCubeToCoordinate, qCubeFacet]
  · simp [qCubeToCoordinate, qCubeFacet, h]

end FiniteChains.Davis
