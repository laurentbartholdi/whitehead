import RequestProject.OrderNerveSmallChainBasis
import RequestProject.NerveDegree

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision
open scoped Classical

noncomputable def orderSmallChosenVertex {P : Type} [PartialOrder P] {n : ℕ}
    (σ : OrderSmallSimplex P n) : P := σ.property.choose

theorem orderSmallChosenVertex_mem {P : Type} [PartialOrder P] {n : ℕ}
    (σ : OrderSmallSimplex P n) :
    orderSmallChosenVertex σ ∈ orderNerveSingularCarrier σ.val :=
  orderNerveSingularStarIndices_subset_carrier σ.val σ.property.choose_spec

/-- The comparison begins by choosing a vertex of a star containing each point. -/
noncomputable def orderSmallToNerve0 {P : Type} [PartialOrder P] :
    smallChains (orderNerveRealizationOpenStar P) 0 →ₗ[ℤ] Nerve.Ch P :=
  (Finsupp.linearCombination ℤ (fun σ : OrderSmallSimplex P 0 =>
    FreeAbelianGroup.of [orderSmallChosenVertex σ])).comp (orderSmallChainEquiv P 0).toLinearMap

theorem orderSmallToNerve0_single {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 0) (r : ℤ) :
    orderSmallToNerve0 (orderSmallSingle σ r) = r • FreeAbelianGroup.of [orderSmallChosenVertex σ] := by
  rw [← orderSmallChainEquiv_symm_single]
  simp only [orderSmallToNerve0, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Finsupp.linearCombination_single]

theorem orderSmallToNerve0_single_carrier {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 0) :
    orderSmallToNerve0 (orderSmallSingle σ 1) ∈ Nerve.IncOn (orderNerveSingularCarrier σ.val) := by
  rw [orderSmallToNerve0_single, one_smul]
  apply Nerve.of_mem_incOn (by simp)
  intro p hp
  have hp' : p = orderSmallChosenVertex σ := by simpa using hp
  rw [hp']
  exact orderSmallChosenVertex_mem σ

theorem orderSmallToNerve0_length {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 0) :
    Nerve.lengthProjection 1 (orderSmallToNerve0 c) = orderSmallToNerve0 c := by
  have he : (Nerve.lengthProjection 1).toIntLinearMap.comp orderSmallToNerve0 =
      (orderSmallToNerve0 : smallChains (orderNerveRealizationOpenStar P) 0 →ₗ[ℤ] Nerve.Ch P) := by
    apply orderSmallSingle_spans
    intro σ
    simp [orderSmallToNerve0_single]
  exact DFunLike.congr_fun he c

theorem orderSmallToNerve0_boundary {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 0) :
    Nerve.bdry (orderSmallToNerve0 c) = augmentation c.val • FreeAbelianGroup.of ([] : List P) := by
  have he : Nerve.bdry.toIntLinearMap.comp orderSmallToNerve0 =
      (augmentation.comp (smallChains (orderNerveRealizationOpenStar P) 0).subtype).smulRight
        (FreeAbelianGroup.of ([] : List P)) := by
    apply orderSmallSingle_spans
    intro σ
    change Nerve.bdry (orderSmallToNerve0 (orderSmallSingle σ 1)) =
      augmentation (Finsupp.single σ.val 1) • FreeAbelianGroup.of ([] : List P)
    rw [orderSmallToNerve0_single, one_smul, augmentation_single, one_smul, Nerve.bdry_of]
    simp [Nerve.bdryOn]
  exact DFunLike.congr_fun he c

/-- Each small one-simplex has an actual nerve filling of its already assigned
endpoint boundary, supported in its own carrier. -/
theorem orderSmallOneFill_exists {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 1) :
    ∃ b : Nerve.Ch P, b ∈ Nerve.IncOn (orderNerveSingularCarrier σ.val) ∧
      Nerve.lengthProjection 2 b = b ∧ Nerve.bdry b =
        orderSmallToNerve0 (smallBoundary (orderNerveRealizationOpenStar P) 0 (orderSmallSingle σ 1)) := by
  let c := orderSmallToNerve0
    (smallBoundary (orderNerveRealizationOpenStar P) 0 (orderSmallSingle σ 1))
  have hc : c ∈ Nerve.IncOn (orderNerveSingularCarrier σ.val) := by
    dsimp only [c]
    rw [orderSmallSingle_boundary, map_sum]
    apply AddSubgroup.sum_mem
    intro i _
    rw [map_zsmul]
    apply AddSubgroup.zsmul_mem
    exact Nerve.incOn_mono (fun _ hp => orderSmallSimplexFace_carrier i σ hp)
      (orderSmallToNerve0_single_carrier (orderSmallSimplexFace i σ))
  have hcycle : Nerve.bdry c = 0 := by
    rw [orderSmallToNerve0_boundary]
    change augmentation (boundary 0 (Finsupp.single σ.val 1)) • _ = 0
    rw [augmentation_boundary, zero_smul]
  obtain ⟨b, hb, he⟩ := orderNerveSingularCarrier_nerve_acyclic σ.val σ.property c hc hcycle
  refine ⟨Nerve.lengthProjection 2 b, Nerve.lengthProjection_mem_incOn _ hb,
    Nerve.lengthProjection_idempotent _ _, ?_⟩
  rw [← Nerve.lengthProjection_bdry, he]
  exact orderSmallToNerve0_length _

noncomputable def orderSmallOneFill {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 1) : Nerve.Ch P := (orderSmallOneFill_exists σ).choose

noncomputable def orderSmallToNerve1 {P : Type} [PartialOrder P] :
    smallChains (orderNerveRealizationOpenStar P) 1 →ₗ[ℤ] Nerve.Ch P :=
  (Finsupp.linearCombination ℤ orderSmallOneFill).comp (orderSmallChainEquiv P 1).toLinearMap

theorem orderSmallToNerve1_single {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 1) (r : ℤ) :
    orderSmallToNerve1 (orderSmallSingle σ r) = r • orderSmallOneFill σ := by
  rw [← orderSmallChainEquiv_symm_single]
  simp only [orderSmallToNerve1, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Finsupp.linearCombination_single]

/-- The constructed low-degree map commutes with the actual singular differential. -/
theorem orderSmallToNerve1_boundary {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 1) :
    Nerve.bdry (orderSmallToNerve1 c) =
      orderSmallToNerve0 (smallBoundary (orderNerveRealizationOpenStar P) 0 c) := by
  have he : Nerve.bdry.toIntLinearMap.comp orderSmallToNerve1 =
      orderSmallToNerve0.comp (smallBoundary (orderNerveRealizationOpenStar P) 0) := by
    apply orderSmallSingle_spans
    intro σ
    simp only [LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap,
      orderSmallToNerve1_single, one_smul]
    exact (orderSmallOneFill_exists σ).choose_spec.2.2
  exact DFunLike.congr_fun he c

end FiniteChains.Comb
