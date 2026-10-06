import RequestProject.OrderTopConeChains

/-! The degree-zero boundary of the actual upper-cone subdivision. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder Q]
  (f : P → Q) (c : Q) (hc : ∀ x, f x ≤ c)

/-- Every radial edge runs from its actual vertex to the chosen top cell. -/
theorem topConeRadialChain_boundary (z : P →₀ ℤ) :
    bdry1 (orderCx Q) (topConeRadialChain f c hc z) =
      Finsupp.mapDomain (fun _ : P => c) z - Finsupp.mapDomain f z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw =>
      rw (config := { transparency := .default }) [map_add, map_add, hz, hw, Finsupp.mapDomain_add, Finsupp.mapDomain_add]
      abel
  | single x n =>
      rw (config := { transparency := .default }) [topConeRadialChain, Finsupp.linearCombination_single, map_smul,
        Finsupp.mapDomain_single, Finsupp.mapDomain_single]
      simp [bdry1, topConeRadialEdge, orderCx, smul_sub]

/-- The negated radial fan fills every mapped augmented zero-cycle. -/
theorem topConeRadialChain_cycle_boundary (z : P →₀ ℤ)
    (hz : Finsupp.mapDomain (fun _ : P => c) z = 0) :
    bdry1 (orderCx Q) (-topConeRadialChain f c hc z) = Finsupp.mapDomain f z := by
  rw (config := { transparency := .default }) [map_neg, topConeRadialChain_boundary, hz, zero_sub, neg_neg]

end FiniteChains.Comb
