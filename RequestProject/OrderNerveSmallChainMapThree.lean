module

public import RequestProject.OrderNerveSmallChainMapTwo

@[expose] public section

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision

theorem orderSmallToNerve2_single_carrier {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 2) :
    orderSmallToNerve2 (orderSmallSingle σ 1) ∈ Nerve.IncOn (orderNerveSingularCarrier σ.val) := by
  rw [orderSmallToNerve2_single, one_smul]
  exact (orderSmallTwoFill_exists σ).choose_spec.1

/-- The cellular approximation extends over small singular three-simplices. -/
theorem orderSmallThreeFill_exists {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 3) :
    ∃ b : Nerve.Ch P, b ∈ Nerve.IncOn (orderNerveSingularCarrier σ.val) ∧
      Nerve.lengthProjection 4 b = b ∧ Nerve.bdry b =
        orderSmallToNerve2 (smallBoundary (orderNerveRealizationOpenStar P) 2 (orderSmallSingle σ 1)) := by
  let c := orderSmallToNerve2
    (smallBoundary (orderNerveRealizationOpenStar P) 2 (orderSmallSingle σ 1))
  have hc : c ∈ Nerve.IncOn (orderNerveSingularCarrier σ.val) := by
    dsimp only [c]
    rw [orderSmallSingle_boundary, map_sum]
    apply AddSubgroup.sum_mem
    intro i _
    rw [map_zsmul]
    apply AddSubgroup.zsmul_mem
    exact Nerve.incOn_mono (fun _ hp => orderSmallSimplexFace_carrier i σ hp)
      (orderSmallToNerve2_single_carrier (orderSmallSimplexFace i σ))
  have hcycle : Nerve.bdry c = 0 := by
    rw [orderSmallToNerve2_boundary]
    have he : smallBoundary (orderNerveRealizationOpenStar P) 1
        (smallBoundary (orderNerveRealizationOpenStar P) 2 (orderSmallSingle σ 1)) = 0 :=
      DFunLike.congr_fun (smallBoundary_squared (orderNerveRealizationOpenStar P) 1)
        (orderSmallSingle σ 1)
    rw [he, map_zero]
  obtain ⟨b, hb, he⟩ := orderNerveSingularCarrier_nerve_acyclic σ.val σ.property c hc hcycle
  refine ⟨Nerve.lengthProjection 4 b, Nerve.lengthProjection_mem_incOn _ hb,
    Nerve.lengthProjection_idempotent _ _, ?_⟩
  rw [← Nerve.lengthProjection_bdry, he]
  exact orderSmallToNerve2_length _

noncomputable def orderSmallThreeFill {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 3) : Nerve.Ch P := (orderSmallThreeFill_exists σ).choose

noncomputable def orderSmallToNerve3 {P : Type} [PartialOrder P] :
    smallChains (orderNerveRealizationOpenStar P) 3 →ₗ[ℤ] Nerve.Ch P :=
  (Finsupp.linearCombination ℤ orderSmallThreeFill).comp (orderSmallChainEquiv P 3).toLinearMap

theorem orderSmallToNerve3_single {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 3) (r : ℤ) :
    orderSmallToNerve3 (orderSmallSingle σ r) = r • orderSmallThreeFill σ := by
  rw [← orderSmallChainEquiv_symm_single]
  simp only [orderSmallToNerve3, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Finsupp.linearCombination_single]

theorem orderSmallToNerve3_boundary {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 3) :
    Nerve.bdry (orderSmallToNerve3 c) =
      orderSmallToNerve2 (smallBoundary (orderNerveRealizationOpenStar P) 2 c) := by
  have he : Nerve.bdry.toIntLinearMap.comp orderSmallToNerve3 =
      orderSmallToNerve2.comp (smallBoundary (orderNerveRealizationOpenStar P) 2) := by
    apply orderSmallSingle_spans
    intro σ
    simp only [LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap,
      orderSmallToNerve3_single, one_smul]
    exact (orderSmallThreeFill_exists σ).choose_spec.2.2
  exact DFunLike.congr_fun he c

theorem orderSmallToNerve3_length {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 3) :
    Nerve.lengthProjection 4 (orderSmallToNerve3 c) = orderSmallToNerve3 c := by
  have he : (Nerve.lengthProjection 4).toIntLinearMap.comp orderSmallToNerve3 =
      (orderSmallToNerve3 : smallChains (orderNerveRealizationOpenStar P) 3 →ₗ[ℤ] Nerve.Ch P) := by
    apply orderSmallSingle_spans
    intro σ
    simp only [LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap,
      orderSmallToNerve3_single, one_smul]
    exact (orderSmallThreeFill_exists σ).choose_spec.2.1
  exact DFunLike.congr_fun he c

theorem orderSmallToNerve3_mem_inc {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 3) : orderSmallToNerve3 c ∈ Nerve.Inc P := by
  obtain ⟨d, rfl⟩ := (orderSmallChainEquiv P 3).symm.surjective c
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => simpa only [map_add] using (Nerve.Inc P).add_mem hd he
  | single σ r =>
    rw [orderSmallChainEquiv_symm_single, orderSmallToNerve3_single]
    exact (Nerve.Inc P).zsmul_mem
      (Nerve.incOn_le_inc _ (orderSmallThreeFill_exists σ).choose_spec.1) r

noncomputable def orderSmallCellularApproximation3 {P : Type} [PartialOrder P] :
    smallChains (orderNerveRealizationOpenStar P) 3 →ₗ[ℤ] (OrdTet P →₀ ℤ) :=
  decodeOrdNerve3.toIntLinearMap.comp orderSmallToNerve3

/-- Boundaries of small three-chains become genuine cellular boundaries. -/
theorem orderSmallCellularApproximation3_boundary {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 3) :
    ordBoundary3 (orderSmallCellularApproximation3 c) =
      orderSmallCellularApproximation2 (smallBoundary (orderNerveRealizationOpenStar P) 2 c) := by
  apply ordNerveChain2_injective
  rw [ordNerveChain2_ordBoundary3]
  change Nerve.bdry (ordNerveChain3 (decodeOrdNerve3 (orderSmallToNerve3 c))) =
    ordNerveChain2 (decodeOrdNerve2 (orderSmallToNerve2 _))
  rw [ordNerveChain3_decode (orderSmallToNerve3_mem_inc c), orderSmallToNerve3_length,
    orderSmallToNerve3_boundary, ordNerveChain2_decode (orderSmallToNerve2_mem_inc _),
    orderSmallToNerve2_length]

end FiniteChains.Comb
