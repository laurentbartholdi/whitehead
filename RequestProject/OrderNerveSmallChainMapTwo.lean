module

public import RequestProject.OrderNerveSmallChainMapLow
public import RequestProject.OrderNerveDecoding

@[expose] public section

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision
open scoped Classical

theorem orderSmallToNerve1_single_carrier {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 1) :
    orderSmallToNerve1 (orderSmallSingle σ 1) ∈ Nerve.IncOn (orderNerveSingularCarrier σ.val) := by
  rw [orderSmallToNerve1_single, one_smul]
  exact (orderSmallOneFill_exists σ).choose_spec.1

theorem orderSmallToNerve1_length {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 1) :
    Nerve.lengthProjection 2 (orderSmallToNerve1 c) = orderSmallToNerve1 c := by
  have he : (Nerve.lengthProjection 2).toIntLinearMap.comp orderSmallToNerve1 =
      (orderSmallToNerve1 : smallChains (orderNerveRealizationOpenStar P) 1 →ₗ[ℤ] Nerve.Ch P) := by
    apply orderSmallSingle_spans
    intro σ
    simp only [LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap,
      orderSmallToNerve1_single, one_smul]
    exact (orderSmallOneFill_exists σ).choose_spec.2.1
  exact DFunLike.congr_fun he c

/-- The boundary assigned to a small two-simplex has an actual triangle
filling in its own carrier. -/
theorem orderSmallTwoFill_exists {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 2) :
    ∃ b : Nerve.Ch P, b ∈ Nerve.IncOn (orderNerveSingularCarrier σ.val) ∧
      Nerve.lengthProjection 3 b = b ∧ Nerve.bdry b =
        orderSmallToNerve1 (smallBoundary (orderNerveRealizationOpenStar P) 1 (orderSmallSingle σ 1)) := by
  let c := orderSmallToNerve1
    (smallBoundary (orderNerveRealizationOpenStar P) 1 (orderSmallSingle σ 1))
  have hc : c ∈ Nerve.IncOn (orderNerveSingularCarrier σ.val) := by
    dsimp only [c]
    rw [orderSmallSingle_boundary, map_sum]
    apply AddSubgroup.sum_mem
    intro i _
    rw [map_zsmul]
    apply AddSubgroup.zsmul_mem
    exact Nerve.incOn_mono (fun _ hp => orderSmallSimplexFace_carrier i σ hp)
      (orderSmallToNerve1_single_carrier (orderSmallSimplexFace i σ))
  have hcycle : Nerve.bdry c = 0 := by
    rw [orderSmallToNerve1_boundary]
    have he : smallBoundary (orderNerveRealizationOpenStar P) 0
        (smallBoundary (orderNerveRealizationOpenStar P) 1 (orderSmallSingle σ 1)) = 0 :=
      DFunLike.congr_fun (smallBoundary_squared (orderNerveRealizationOpenStar P) 0)
        (orderSmallSingle σ 1)
    rw [he, map_zero]
  obtain ⟨b, hb, he⟩ := orderNerveSingularCarrier_nerve_acyclic σ.val σ.property c hc hcycle
  refine ⟨Nerve.lengthProjection 3 b, Nerve.lengthProjection_mem_incOn _ hb,
    Nerve.lengthProjection_idempotent _ _, ?_⟩
  rw [← Nerve.lengthProjection_bdry, he]
  exact orderSmallToNerve1_length _

noncomputable def orderSmallTwoFill {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 2) : Nerve.Ch P := (orderSmallTwoFill_exists σ).choose

noncomputable def orderSmallToNerve2 {P : Type} [PartialOrder P] :
    smallChains (orderNerveRealizationOpenStar P) 2 →ₗ[ℤ] Nerve.Ch P :=
  (Finsupp.linearCombination ℤ orderSmallTwoFill).comp (orderSmallChainEquiv P 2).toLinearMap

theorem orderSmallToNerve2_single {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 2) (r : ℤ) :
    orderSmallToNerve2 (orderSmallSingle σ r) = r • orderSmallTwoFill σ := by
  rw [← orderSmallChainEquiv_symm_single]
  simp only [orderSmallToNerve2, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Finsupp.linearCombination_single]

theorem orderSmallToNerve2_boundary {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 2) :
    Nerve.bdry (orderSmallToNerve2 c) =
      orderSmallToNerve1 (smallBoundary (orderNerveRealizationOpenStar P) 1 c) := by
  have he : Nerve.bdry.toIntLinearMap.comp orderSmallToNerve2 =
      orderSmallToNerve1.comp (smallBoundary (orderNerveRealizationOpenStar P) 1) := by
    apply orderSmallSingle_spans
    intro σ
    simp only [LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap,
      orderSmallToNerve2_single, one_smul]
    exact (orderSmallTwoFill_exists σ).choose_spec.2.2
  exact DFunLike.congr_fun he c

theorem orderSmallToNerve2_length {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 2) :
    Nerve.lengthProjection 3 (orderSmallToNerve2 c) = orderSmallToNerve2 c := by
  have he : (Nerve.lengthProjection 3).toIntLinearMap.comp orderSmallToNerve2 =
      (orderSmallToNerve2 : smallChains (orderNerveRealizationOpenStar P) 2 →ₗ[ℤ] Nerve.Ch P) := by
    apply orderSmallSingle_spans
    intro σ
    simp only [LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap,
      orderSmallToNerve2_single, one_smul]
    exact (orderSmallTwoFill_exists σ).choose_spec.2.1
  exact DFunLike.congr_fun he c

theorem orderSmallToNerve2_mem_inc {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 2) : orderSmallToNerve2 c ∈ Nerve.Inc P := by
  obtain ⟨d, rfl⟩ := (orderSmallChainEquiv P 2).symm.surjective c
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => simpa only [map_add] using (Nerve.Inc P).add_mem hd he
  | single σ r =>
    rw [orderSmallChainEquiv_symm_single, orderSmallToNerve2_single]
    exact (Nerve.Inc P).zsmul_mem
      (Nerve.incOn_le_inc _ (orderSmallTwoFill_exists σ).choose_spec.1) r

/-- A concrete order-cell two-chain assigned to each star-small singular chain. -/
noncomputable def orderSmallCellularApproximation2 {P : Type} [PartialOrder P] :
    smallChains (orderNerveRealizationOpenStar P) 2 →ₗ[ℤ] (OrdTri P →₀ ℤ) :=
  decodeOrdNerve2.toIntLinearMap.comp orderSmallToNerve2

/-- The assigned order-cell chain is a cycle whenever the original small
singular chain is a cycle. Homological comparison still requires a homotopy. -/
theorem orderSmallCellularApproximation2_cycle {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 2)
    (hc : smallBoundary (orderNerveRealizationOpenStar P) 1 c = 0) :
    bdry2 (orderCx P) (orderSmallCellularApproximation2 c) = 0 := by
  apply (ordNerveChain2_cycle_iff _).mp
  change Nerve.bdry (ordNerveChain2 (decodeOrdNerve2 (orderSmallToNerve2 c))) = 0
  rw [ordNerveChain2_decode (orderSmallToNerve2_mem_inc c), orderSmallToNerve2_length,
    orderSmallToNerve2_boundary, hc, map_zero]

end FiniteChains.Comb
