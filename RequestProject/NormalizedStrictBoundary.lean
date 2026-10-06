import RequestProject.OrderNormalizationNaturality
import RequestProject.OrderComparableOneHomotopy

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

/-- Actual cellular normalization and an actual monotone endomorphism commute
with the genuine two-to-one boundary. -/
theorem bdry2_normalizedStrictChain2 (g : P → P) (hg : Monotone g)
    (c : StrictOrdTri P →₀ ℤ) :
    bdry2 (strictOrderCx P) (normalizedStrictChain2 g hg c) =
      normalizedStrictChain1 g hg (bdry2 (strictOrderCx P) c) := by
  change bdry2 (strictOrderCx P)
    (normalizeOrdChain2 (chain2 (orderCxMap g hg) (chain2 (strictOrderIncl P) c))) =
    normalizeOrdChain1 (chain1 (orderCxMap g hg)
      (chain1 (strictOrderIncl P) (bdry2 (strictOrderCx P) c)))
  rw [bdry2_normalizeOrdChain2, bdry2_chain2, bdry2_chain2]

end FiniteChains.Comb
