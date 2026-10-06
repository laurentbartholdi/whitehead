import RequestProject.TopologicalSingular.HurewiczIsomorphism
import RequestProject.OrderNerveSingularH2Iso
import RequestProject.OrderUniversalRealizationSimplyConnected

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular

/-- Actual pi2 of a simply connected order-nerve realization is its integral
order-chain H2, through the canonical singular realization comparison. -/
noncomputable def orderRealizationPi2OrderH2Equiv (P : Type) [PartialOrder P]
    [SimplyConnectedSpace (orderNerveRealization P)] (x : orderNerveRealization P) :
    Additive (HomotopyGroup (Fin 2) (orderNerveRealization P) x) ≃ₗ[ℤ] OrderNerveH2 P :=
  (singularHurewicz2LinearEquiv x).trans (orderCellSingularH2Equiv P).symm

theorem orderRealizationPi2OrderH2Equiv_natural {P Q : Type} [PartialOrder P] [PartialOrder Q]
    [SimplyConnectedSpace (orderNerveRealization P)] [SimplyConnectedSpace (orderNerveRealization Q)]
    (f : P → Q) (hf : Monotone f) (x : orderNerveRealization P)
    (q : Additive (HomotopyGroup (Fin 2) (orderNerveRealization P) x)) :
    orderRealizationPi2OrderH2Equiv Q (orderNerveRealizationMap f hf x)
      (Additive.ofMul (Whitehead.pi2Map
        ⟨orderNerveRealizationMap f hf, (orderNerveRealizationMap f hf).hom.continuous⟩ x q.toMul)) =
      orderNerveH2Map f hf (orderRealizationPi2OrderH2Equiv P x q) := by
  apply (orderCellSingularH2Equiv Q).injective
  rw [← orderCellSingularH2Equiv_natural f hf]
  simp only [orderRealizationPi2OrderH2Equiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, singularHurewicz2LinearEquiv_apply]
  exact (singularHurewicz2_natural
    ⟨orderNerveRealizationMap f hf, (orderNerveRealizationMap f hf).hom.continuous⟩ x q.toMul).symm

/-- Apply the genuine Hurewicz comparison to the constructed universal order
cover; its simple connectedness is a proved property of its realization. -/
noncomputable def uOrderRealizationPi2OrderH2Equiv {P : Type} [PartialOrder P] (a : P)
    (x : orderNerveRealization (UOrder P a)) :
    Additive (HomotopyGroup (Fin 2) (orderNerveRealization (UOrder P a)) x) ≃ₗ[ℤ]
      OrderNerveH2 (UOrder P a) := by
  letI := uOrderRealization_simplyConnected a
  exact orderRealizationPi2OrderH2Equiv (UOrder P a) x

end FiniteChains.Comb
