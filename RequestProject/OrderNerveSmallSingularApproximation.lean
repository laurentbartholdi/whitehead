import RequestProject.OrderNerveCellularSingularSupport
import RequestProject.OrderNerveCellularSingularZero

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision

noncomputable def orderSmallSingularApproximation1 {P : Type} [PartialOrder P] :
    smallChains (orderNerveRealizationOpenStar P) 1 →ₗ[ℤ] Chain (orderNerveRealization P) 1 :=
  orderCellSingularChain1.comp orderSmallCellularApproximation1

noncomputable def orderSmallSingularApproximation2 {P : Type} [PartialOrder P] :
    smallChains (orderNerveRealizationOpenStar P) 2 →ₗ[ℤ] Chain (orderNerveRealization P) 2 :=
  orderCellSingularChain2.comp orderSmallCellularApproximation2

theorem orderSmallSingularApproximation1_boundary {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 1) :
    boundary 0 (orderSmallSingularApproximation1 c) =
      orderSmallSingularApproximation0 (smallBoundary (orderNerveRealizationOpenStar P) 0 c) := by
  change boundary 0 (orderCellSingularChain1 (orderSmallCellularApproximation1 c)) = _
  rw [orderCellSingularChain1_boundary, orderSmallCellularApproximation1_boundary,
    orderSmallSingularApproximation0_realization]

theorem orderSmallSingularApproximation2_boundary {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 2) :
    boundary 1 (orderSmallSingularApproximation2 c) =
      orderSmallSingularApproximation1 (smallBoundary (orderNerveRealizationOpenStar P) 1 c) := by
  change boundary 1 (orderCellSingularChain2 (orderSmallCellularApproximation2 c)) = _
  rw [orderCellSingularChain2_boundary, orderSmallCellularApproximation2_boundary]
  rfl

theorem orderSmallSingularApproximation1_carrier {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 1) :
    orderSmallSingularApproximation1 (orderSmallSingle σ 1) ∈
      orderSingularCarrierChains σ.val 1 := by
  change orderCellSingularChain1 (decodeOrdNerve1 (orderSmallToNerve1 (orderSmallSingle σ 1))) ∈ _
  exact orderCellSingularDecode1_supported _ (orderSmallToNerve1_single_carrier σ)

theorem orderSmallSingularApproximation2_carrier {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 2) :
    orderSmallSingularApproximation2 (orderSmallSingle σ 1) ∈
      orderSingularCarrierChains σ.val 2 := by
  change orderCellSingularChain2 (decodeOrdNerve2 (orderSmallToNerve2 (orderSmallSingle σ 1))) ∈ _
  exact orderCellSingularDecode2_supported _ (orderSmallToNerve2_single_carrier σ)

/-- A carried linear map sends every simplex boundary into the parent carrier. -/
theorem orderSmallBoundary_map_carrier {P : Type} [PartialOrder P] {n k : ℕ}
    (H : smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ] Chain (orderNerveRealization P) k)
    (hH : ∀ τ : OrderSmallSimplex P n,
      H (orderSmallSingle τ 1) ∈ orderSingularCarrierChains τ.val k)
    (σ : OrderSmallSimplex P (n + 1)) :
    H (smallBoundary (orderNerveRealizationOpenStar P) n (orderSmallSingle σ 1)) ∈
      orderSingularCarrierChains σ.val k := by
  rw [orderSmallSingle_boundary, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  apply Submodule.smul_mem
  exact orderSingularCarrierChains_face σ.val i k (hH (orderSmallSimplexFace i σ))

end FiniteChains.Comb
