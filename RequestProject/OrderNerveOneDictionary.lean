import RequestProject.OrderNerveCellMaps
import RequestProject.CellularChainMapZero

/-! The degree-one dictionary for actual order chains and their finite prisms. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

noncomputable def ordNerveChain0 : (P →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  Finsupp.linearCombination ℤ (fun p => FreeAbelianGroup.of [p])

theorem ordNerveChain0_bdry1 (c : OrdEdge P →₀ ℤ) :
    ordNerveChain0 (bdry1 (orderCx P) c) = Nerve.bdry (ordNerveChain1 c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single e n =>
    rw [bdry1_single]
    simp only [map_smul, map_sub]
    simp [ordNerveChain0, ordNerveChain1, orderCx, Nerve.bdryOn,
      Nerve.consMap_of, smul_sub, map_sub, Finsupp.linearCombination_single]

theorem ordNerveChain1_mem_inc (c : OrdEdge P →₀ ℤ) :
    ordNerveChain1 c ∈ Nerve.Inc P := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add] using AddSubgroup.add_mem _ hc hd
  | single e n =>
    simp only [ordNerveChain1, Finsupp.linearCombination_single]
    apply AddSubgroup.zsmul_mem
    apply Nerve.of_mem_inc
    simpa [List.isChain_cons] using e.2

theorem ordNerveChain1_lengthProjection (c : OrdEdge P →₀ ℤ) :
    Nerve.lengthProjection 2 (ordNerveChain1 c) = ordNerveChain1 c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single e n => simp [ordNerveChain1]

theorem ordNerveChain1_chain1 (f : P → Q) (hf : Monotone f) (c : OrdEdge P →₀ ℤ) :
    ordNerveChain1 (chain1 (orderCxMap f hf) c) = Nerve.cmap f (ordNerveChain1 c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, map_add]
  | single e n =>
    change ordNerveChain1 (Finsupp.mapDomain (orderCxMap f hf).onE
      (Finsupp.single e n)) = _
    rw [Finsupp.mapDomain_single]
    simp [ordNerveChain1, Nerve.cmap_of, orderCxMap]

end FiniteChains.Comb
