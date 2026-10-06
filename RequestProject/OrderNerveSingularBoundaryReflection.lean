import RequestProject.OrderNerveReturnHomotopy

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular
variable {P : Type} [PartialOrder P]

/-- A genuine singular filling of a realized simplicial cycle produces an
actual simplicial filling, in every positive dimension. -/
theorem orderNerveExplicitSingular_reflects_boundaries (n : ℕ)
    (c : ComposableArrows P (n + 1) →₀ ℤ) (hc : orderSimplicialBoundary P n c = 0)
    (b : Chain (orderNerveRealization P) (n + 2))
    (hb : boundary (n + 1) b = (orderNerveExplicitSingularMap P).f (n + 1) c) :
    ∃ a : ComposableArrows P (n + 2) →₀ ℤ, orderSimplicialBoundary P (n + 1) a = c := by
  let w := orderSingularToNerve P (n + 2) b + orderReturnHomotopy P (n + 1) c
  have hw : w ∈ Nerve.Inc P := AddSubgroup.add_mem _
    (orderSingularToNerve_mem_inc _ _) (orderReturnHomotopy_mem_inc _ _)
  have hd : Nerve.bdry w = orderNerveGradedEncode (n + 1) c := by
    dsimp only [w]
    rw (config := { transparency := .default }) [map_add, orderSingularToNerve_boundary, hb, orderReturnHomotopy_identity,
      hc, map_zero, sub_zero]
    change orderNerveRoundTrip P (n + 1) c +
      (orderNerveGradedEncode (n + 1) c - orderNerveRoundTrip P (n + 1) c) = _
    abel
  refine ⟨orderNerveGradedDecode (n + 2) w, ?_⟩
  apply orderNerveGradedEncode_injective (n + 1)
  rw (config := { transparency := .default }) [orderNerveGradedEncode_boundary, orderNerveGradedEncode_decode _ hw,
    ← Nerve.lengthProjection_bdry, hd, orderNerveGradedEncode_length]

end FiniteChains.Comb
