import RequestProject.OrderNerveSmallHomotopyTwo

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision

/-- Every actual singular two-cycle in an arbitrary order realization is
homologous to a realized finite cellular two-cycle. No local finiteness is used. -/
theorem orderNerveRealization_twoCycle_cellularRepresentative {P : Type} [PartialOrder P]
    (c : Chain (orderNerveRealization P) 2) (hc : boundary 1 c = 0) :
    ∃ z : OrdTri P →₀ ℤ, bdry2 (orderCx P) z = 0 ∧
      ∃ b : Chain (orderNerveRealization P) 3, boundary 2 b = c - orderCellSingularChain2 z := by
  obtain ⟨d, hd, hz, a, ha⟩ := orderNerveRealization_exists_small_cycle P 1 c hc
  let d' : smallChains (orderNerveRealizationOpenStar P) 2 := ⟨d, hd⟩
  have hd' : smallBoundary (orderNerveRealizationOpenStar P) 1 d' = 0 := Subtype.ext hz
  obtain ⟨b, hb⟩ := orderSmallCellularApproximation2_homologous d' hd'
  refine ⟨orderSmallCellularApproximation2 d', orderSmallCellularApproximation2_cycle d' hd',
    b - a, ?_⟩
  rw [map_sub, hb, ha]
  change d - orderCellSingularChain2 (orderSmallCellularApproximation2 d') - (d - c) = _
  abel

end FiniteChains.Comb
