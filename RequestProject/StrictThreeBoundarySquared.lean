module

public import RequestProject.StrictTopConeThreeChains

@[expose] public section

/-! Boundary squared vanishes for genuine nondegenerate order tetrahedra. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

theorem strictOrdTetBoundary_cycle (t : StrictOrdTet P) :
    bdry2 (strictOrderCx P) (strictOrdTetBoundary t) = 0 := by
  rw (config := { transparency := .default }) [strictOrdTetBoundary, map_sub, map_add, map_sub]
  simp only [bdry2_single (X := strictOrderCx P), one_smul]
  simp [strictOrderCx, pathChain]
  abel

theorem strictOrdBoundary3_cycle (z : StrictOrdTet P →₀ ℤ) :
    bdry2 (strictOrderCx P) (strictOrdBoundary3 z) = 0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw, add_zero]
  | single t n =>
      rw (config := { transparency := .default }) [strictOrdBoundary3, Finsupp.linearCombination_single, map_smul,
        strictOrdTetBoundary_cycle, smul_zero]

end FiniteChains.Comb
