import RequestProject.OrderUniversalPosetHom
import RequestProject.StrictOrderChains

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

/-- Genuine finite lifted-order chains and path-class cover chains are linearly equivalent. -/
noncomputable def uOrderChain2Equiv :
    (OrdTri (UOrder P a) →₀ ℤ) ≃ₗ[ℤ] (UF (orderCx P) a →₀ ℤ) :=
  LinearEquiv.ofBijective (chain2 uOrderHom)
    ⟨uOrderHom_chain2_injective, uOrderHom_chain2_surjective⟩

theorem uOrderChain2Equiv_apply (c : OrdTri (UOrder P a) →₀ ℤ) :
    uOrderChain2Equiv c = chain2 uOrderHom c := rfl

/-- Normalize the actual universal-cover chain through its actual lifted-order coordinates. -/
noncomputable def uOrderNormalizeChain2 :
    (UF (orderCx P) a →₀ ℤ) →ₗ[ℤ] (StrictOrdTri (UOrder P a) →₀ ℤ) :=
  normalizeOrdChain2.comp uOrderChain2Equiv.symm.toLinearMap

theorem uOrderNormalizeChain2_cycle (c : UF (orderCx P) a →₀ ℤ)
    (hc : bdry2 (uCover (orderCx P) a) c = 0) :
    bdry2 (strictOrderCx (UOrder P a)) (uOrderNormalizeChain2 c) = 0 := by
  apply normalizeOrdChain2_cycle
  apply (uOrderHom_cycle_iff _).mp
  change bdry2 (uCover (orderCx P) a)
    (uOrderChain2Equiv (uOrderChain2Equiv.symm c)) = 0
  rw [uOrderChain2Equiv.apply_symm_apply]
  exact hc

/-- Actual strict chains retain every coefficient under the cover comparison and normalization. -/
theorem uOrderNormalizeChain2_inclusion (c : StrictOrdTri (UOrder P a) →₀ ℤ) :
    uOrderNormalizeChain2
      (chain2 uOrderHom (Finsupp.mapDomain (strictOrderIncl (UOrder P a)).onF c)) = c := by
  change normalizeOrdChain2 (uOrderChain2Equiv.symm
    (uOrderChain2Equiv (Finsupp.mapDomain (strictOrderIncl (UOrder P a)).onF c))) = c
  rw [uOrderChain2Equiv.symm_apply_apply, normalizeOrdChain2_inclusion]

end FiniteChains.Comb
