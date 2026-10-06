module

public import RequestProject.OrderUniversalChainNormalization

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

/-- The genuine universal-cover chain identification preserves the actual projection. -/
theorem uOrderChain2Equiv_projection (c : OrdTri (UOrder P a) →₀ ℤ) :
    chain2 (univProj (X := orderCx P) (x₀ := a)) (uOrderChain2Equiv c) =
      chain2 (orderCxMap uOrderEnd uOrderEnd_monotone) c := by
  change Finsupp.mapDomain (univProj (X := orderCx P) (x₀ := a)).onF (Finsupp.mapDomain uOrderHom.onF c) = _
  rw [← Finsupp.mapDomain_comp]
  rfl

end FiniteChains.Comb
