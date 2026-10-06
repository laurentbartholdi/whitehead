import RequestProject.OrderNerveSingularCarriers
import RequestProject.TopologicalSingular.SupportedFillings

namespace FiniteChains.Comb
open TopologicalSingular

noncomputable def orderSingularCarrierChains {P : Type} [PartialOrder P] {n : ℕ}
    (σ : Simplex (orderNerveRealization P) n) (k : ℕ) :
    Submodule ℤ (Chain (orderNerveRealization P) k) :=
  subChains (orderNerveRealizationSubcomplex P (orderNerveSingularCarrier σ) :
    Set (orderNerveRealization P)) k

theorem orderSingularCarrierChains_face {P : Type} [PartialOrder P] {n : ℕ}
    (σ : Simplex (orderNerveRealization P) (n + 1)) (i : Fin (n + 2)) (k : ℕ) :
    orderSingularCarrierChains (face i σ) k ≤ orderSingularCarrierChains σ k :=
  subChains_mono (orderNerveRealizationSubcomplex_mono (orderNerveSingularCarrier_face σ i)) k

theorem orderSingularCarrierChains_single {P : Type} [PartialOrder P] {n : ℕ}
    (σ : Simplex (orderNerveRealization P) n) (r : ℤ) :
    Finsupp.single σ r ∈ orderSingularCarrierChains σ n :=
  single_mem_subChains _ n σ r (orderNerveSingularSimplex_mem_carrier σ)

theorem orderSingularCarrierChains_cycle_bounds {P : Type} [PartialOrder P] {n : ℕ}
    (σ : Simplex (orderNerveRealization P) n)
    (hσ : (orderNerveSingularStarIndices σ).Nonempty) (k : ℕ)
    (c : Chain (orderNerveRealization P) (k + 1))
    (hc : c ∈ orderSingularCarrierChains σ (k + 1)) (hz : boundary k c = 0) :
    ∃ b : Chain (orderNerveRealization P) (k + 2),
      b ∈ orderSingularCarrierChains σ (k + 2) ∧ boundary (k + 1) b = c := by
  letI := orderNerveSingularCarrier_subcomplex_contractible σ hσ
  exact contractible_supported_cycle_bounds _ k c hc hz

theorem orderSingularCarrierChains_zero_bounds {P : Type} [PartialOrder P] {n : ℕ}
    (σ : Simplex (orderNerveRealization P) n)
    (hσ : (orderNerveSingularStarIndices σ).Nonempty)
    (c : Chain (orderNerveRealization P) 0)
    (hc : c ∈ orderSingularCarrierChains σ 0) (hz : augmentation c = 0) :
    ∃ b : Chain (orderNerveRealization P) 1,
      b ∈ orderSingularCarrierChains σ 1 ∧ boundary 0 b = c := by
  letI := orderNerveSingularCarrier_subcomplex_contractible σ hσ
  exact connected_supported_zero_bounds _ c hc hz

end FiniteChains.Comb
