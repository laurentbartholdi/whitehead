import RequestProject.OrderNerveGradedBoundary
import RequestProject.OrderNerveSmallChainMapAll
import RequestProject.OrderNerveSmallSingularApproximation

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory TopologicalSingular SingularSubdivision
variable {P : Type} [PartialOrder P]

/-- Realization of the carried small-chain approximation in every degree. -/
noncomputable def orderSmallSingularApproximation (P : Type) [PartialOrder P] (n : ℕ) :
    smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ] Chain (orderNerveRealization P) n :=
  (orderNerveGradedRealize P n).comp (orderSmallToNerve P n)

theorem orderSmallSingularApproximation_boundary (n : ℕ)
    (c : smallChains (orderNerveRealizationOpenStar P) (n + 1)) :
    boundary n (orderSmallSingularApproximation P (n + 1) c) =
      orderSmallSingularApproximation P n (smallBoundary (orderNerveRealizationOpenStar P) n c) := by
  change boundary n (orderNerveGradedRealize P (n + 1) (orderSmallToNerve P (n + 1) c)) = _
  rw (config := { transparency := .default }) [orderNerveGradedRealize_boundary n (orderSmallToNerve_mem_inc (n + 1) c),
    orderSmallToNerve_boundary]
  rfl

theorem orderSmallSingularApproximation_carrier (n : ℕ) (σ : OrderSmallSimplex P n) :
    orderSmallSingularApproximation P n (orderSmallSingle σ 1) ∈
      orderSingularCarrierChains σ.val n :=
  orderNerveGradedRealize_supported n _ (orderSmallToNerve_carrier n σ)

theorem orderSmallSingularApproximation_zero :
    orderSmallSingularApproximation P 0 = orderSmallSingularApproximation0 := by
  apply orderSmallSingle_spans
  intro σ
  change orderNerveGradedRealize P 0 (orderSmallToNerve0 (orderSmallSingle σ 1)) = _
  rw (config := { transparency := .default }) [orderSmallToNerve0_single, one_smul, orderSmallSingularApproximation0_single]
  have hl : orderNerveVertexList (ComposableArrows.mk₀ (orderSmallChosenVertex σ)) =
      [orderSmallChosenVertex σ] := by simp [orderNerveVertexList, List.ofFn_succ]
  change (orderNerveExplicitSingularMap P).f 0
    (orderNerveGradedDecode 0 (FreeAbelianGroup.of [orderSmallChosenVertex σ])) = _
  rw (config := { transparency := .default }) [orderNerveGradedDecode_of, ← hl, orderNerveGradedDecodeList_vertexList,
    orderNerveExplicitSingularMap_single]
  rfl

end FiniteChains.Comb
