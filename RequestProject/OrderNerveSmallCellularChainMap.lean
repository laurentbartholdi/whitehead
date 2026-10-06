module

public import RequestProject.OrderNerveSmallChainMapThree
public import RequestProject.OrderNerveDecodingLow

@[expose] public section

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision

noncomputable def orderSmallCellularApproximation0 {P : Type} [PartialOrder P] :
    smallChains (orderNerveRealizationOpenStar P) 0 →ₗ[ℤ] (P →₀ ℤ) :=
  decodeOrdNerve0.toIntLinearMap.comp orderSmallToNerve0

noncomputable def orderSmallCellularApproximation1 {P : Type} [PartialOrder P] :
    smallChains (orderNerveRealizationOpenStar P) 1 →ₗ[ℤ] (OrdEdge P →₀ ℤ) :=
  decodeOrdNerve1.toIntLinearMap.comp orderSmallToNerve1

theorem orderSmallCellularApproximation0_single {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 0) (r : ℤ) :
    orderSmallCellularApproximation0 (orderSmallSingle σ r) =
      Finsupp.single (orderSmallChosenVertex σ) r := by
  change decodeOrdNerve0 (orderSmallToNerve0 (orderSmallSingle σ r)) = _
  rw [orderSmallToNerve0_single, map_zsmul, decodeOrdNerve0_of]
  simp [decodeOrdVertexList]

theorem orderSmallToNerve1_mem_inc {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 1) : orderSmallToNerve1 c ∈ Nerve.Inc P := by
  obtain ⟨d, rfl⟩ := (orderSmallChainEquiv P 1).symm.surjective c
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => simpa only [map_add] using (Nerve.Inc P).add_mem hd he
  | single σ r =>
    rw [orderSmallChainEquiv_symm_single, orderSmallToNerve1_single]
    exact (Nerve.Inc P).zsmul_mem
      (Nerve.incOn_le_inc _ (orderSmallOneFill_exists σ).choose_spec.1) r

theorem orderSmallCellularApproximation1_boundary {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 1) :
    bdry1 (orderCx P) (orderSmallCellularApproximation1 c) =
      orderSmallCellularApproximation0 (smallBoundary (orderNerveRealizationOpenStar P) 0 c) := by
  apply ordNerveChain0_injective
  rw [ordNerveChain0_bdry1]
  change Nerve.bdry (ordNerveChain1 (decodeOrdNerve1 (orderSmallToNerve1 c))) =
    ordNerveChain0 (decodeOrdNerve0 (orderSmallToNerve0 _))
  rw [ordNerveChain1_decode (orderSmallToNerve1_mem_inc c), orderSmallToNerve1_length,
    orderSmallToNerve1_boundary, ordNerveChain0_decode, orderSmallToNerve0_length]

theorem orderSmallCellularApproximation2_boundary {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 2) :
    bdry2 (orderCx P) (orderSmallCellularApproximation2 c) =
      orderSmallCellularApproximation1 (smallBoundary (orderNerveRealizationOpenStar P) 1 c) := by
  apply ordNerveChain1_injective
  rw [ordNerveChain1_bdry2]
  change Nerve.bdry (ordNerveChain2 (decodeOrdNerve2 (orderSmallToNerve2 c))) =
    ordNerveChain1 (decodeOrdNerve1 (orderSmallToNerve1 _))
  rw [ordNerveChain2_decode (orderSmallToNerve2_mem_inc c), orderSmallToNerve2_length,
    orderSmallToNerve2_boundary, ordNerveChain1_decode (orderSmallToNerve1_mem_inc _),
    orderSmallToNerve1_length]

end FiniteChains.Comb
