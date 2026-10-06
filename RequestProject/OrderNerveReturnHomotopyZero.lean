module

public import RequestProject.OrderNerveSimplicialCarriers

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular
variable {P : Type} [PartialOrder P]

structure OrderReturnHomotopyStage (P : Type) [PartialOrder P] (n : ℕ) where
  map : (ComposableArrows P n →₀ ℤ) →ₗ[ℤ] Nerve.Ch P
  carrier : ∀ s, map (Finsupp.single s 1) ∈ Nerve.IncOn (Set.range s.obj)
  homogeneous : ∀ c, Nerve.lengthProjection (n + 2) (map c) = map c
  on_boundary : ∀ c : ComposableArrows P (n + 1) →₀ ℤ,
    Nerve.bdry (map (orderSimplicialBoundary P n c)) =
      orderNerveGradedEncode n (orderSimplicialBoundary P n c) -
        orderNerveRoundTrip P n (orderSimplicialBoundary P n c)

theorem orderNerveCarriedFill {n : ℕ} (s : ComposableArrows P n) (c : Nerve.Ch P)
    (hc : c ∈ Nerve.IncOn (Set.range s.obj)) (hlen : Nerve.lengthProjection (n + 1) c = c)
    (hz : Nerve.bdry c = 0) :
    ∃ b : Nerve.Ch P, b ∈ Nerve.IncOn (Set.range s.obj) ∧
      Nerve.lengthProjection (n + 2) b = b ∧ Nerve.bdry b = c := by
  obtain ⟨b, hb, he⟩ := orderNerveSimplexCarrier_acyclic s c hc hz
  refine ⟨Nerve.lengthProjection (n + 2) b, Nerve.lengthProjection_mem_incOn _ hb,
    Nerve.lengthProjection_idempotent _ _, ?_⟩
  rw [← Nerve.lengthProjection_bdry, he, hlen]

theorem orderReturnHomotopyZero_fill (s : ComposableArrows P 0) :
    ∃ b : Nerve.Ch P, b ∈ Nerve.IncOn (Set.range s.obj) ∧
      Nerve.lengthProjection 2 b = b ∧ Nerve.bdry b =
        orderNerveGradedEncode 0 (Finsupp.single s 1) - orderNerveRoundTrip P 0 (Finsupp.single s 1) := by
  apply orderNerveCarriedFill s
  · exact AddSubgroup.sub_mem _ (orderNerveGradedEncode_single_supported 0 s)
      (orderNerveRoundTrip_supported 0 s)
  · rw [map_sub, orderNerveGradedEncode_length]
    congr 1
    exact orderSingularToNerve_length 0 _
  · rw [map_sub, orderNerveRoundTrip_zero_boundary, sub_self]

noncomputable def orderReturnHomotopyZero : (ComposableArrows P 0 →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  Finsupp.linearCombination ℤ (fun s => (orderReturnHomotopyZero_fill s).choose)

theorem orderReturnHomotopyZero_single (s : ComposableArrows P 0) :
    orderReturnHomotopyZero (Finsupp.single s 1) = (orderReturnHomotopyZero_fill s).choose := by
  rw [orderReturnHomotopyZero, Finsupp.linearCombination_single, one_smul]

theorem orderReturnHomotopyZero_identity (c : ComposableArrows P 0 →₀ ℤ) :
    Nerve.bdry (orderReturnHomotopyZero c) = orderNerveGradedEncode 0 c - orderNerveRoundTrip P 0 c := by
  have he : Nerve.bdry.toIntLinearMap.comp orderReturnHomotopyZero =
      orderNerveGradedEncode 0 - orderNerveRoundTrip P 0 := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.sub_apply]
    change Nerve.bdry (orderReturnHomotopyZero (Finsupp.single s 1)) = _
    rw [orderReturnHomotopyZero_single]
    exact (orderReturnHomotopyZero_fill s).choose_spec.2.2
  exact DFunLike.congr_fun he c

noncomputable def orderReturnHomotopyStageZero : OrderReturnHomotopyStage P 0 where
  map := orderReturnHomotopyZero
  carrier s := by
    rw [orderReturnHomotopyZero_single]
    exact (orderReturnHomotopyZero_fill s).choose_spec.1
  homogeneous c := by
    have he : (Nerve.lengthProjection 2).toIntLinearMap.comp orderReturnHomotopyZero =
        (orderReturnHomotopyZero : (ComposableArrows P 0 →₀ ℤ) →ₗ[ℤ] Nerve.Ch P) := by
      apply Finsupp.lhom_ext'
      intro s
      apply LinearMap.ext_ring
      simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
      change Nerve.lengthProjection 2 (orderReturnHomotopyZero (Finsupp.single s 1)) = _
      rw [orderReturnHomotopyZero_single]
      exact (orderReturnHomotopyZero_fill s).choose_spec.2.1
    exact DFunLike.congr_fun he c
  on_boundary c := orderReturnHomotopyZero_identity _

end FiniteChains.Comb
