module

public import RequestProject.OrderNerveCellularSingularChains
public import RequestProject.OrderNerveSingularCarrierExactness
public import RequestProject.OrderNerveDecoding

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory TopologicalSingular

theorem orderCellSingularDecode1List_supported {P : Type} [PartialOrder P]
    (A : Set P) (l : List P) (hl : l.IsChain (· ≤ ·)) (hv : ∀ p ∈ l, p ∈ A) :
    orderCellSingularChain1 (decodeOrdEdgeList l) ∈
      subChains (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) 1 := by
  classical
  cases l with
  | nil => simp [decodeOrdEdgeList]
  | cons a l =>
    cases l with
    | nil => simp [decodeOrdEdgeList]
    | cons b l =>
      cases l with
      | cons c l => simp [decodeOrdEdgeList]
      | nil =>
        have hab : a ≤ b := by simpa [List.isChain_cons] using hl
        rw (config := { transparency := .default }) [decodeOrdEdgeList, dif_pos hab, orderCellSingularChain1_single]
        apply single_mem_subChains
        intro z
        apply orderNerveSingularSimplex_supported
        intro i
        fin_cases i
        · exact hv a (by simp)
        · exact hv b (by simp)

/-- Realizing an increasing one-chain preserves every vertex carrier. -/
theorem orderCellSingularDecode1_supported {P : Type} [PartialOrder P]
    (A : Set P) {c : Nerve.Ch P} (hc : c ∈ Nerve.IncOn A) :
    orderCellSingularChain1 (decodeOrdNerve1 c) ∈
      subChains (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) 1 := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, hl, rfl⟩
    rw (config := { transparency := .default }) [decodeOrdNerve1_of]
    exact orderCellSingularDecode1List_supported A l hl.1 hl.2
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | neg x _ hx => simpa only [map_neg] using Submodule.neg_mem _ hx

theorem orderCellSingularDecode2List_supported {P : Type} [PartialOrder P]
    (A : Set P) (l : List P) (hl : l.IsChain (· ≤ ·)) (hv : ∀ p ∈ l, p ∈ A) :
    orderCellSingularChain2 (decodeOrdTriList l) ∈
      subChains (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) 2 := by
  classical
  cases l with
  | nil => simp [decodeOrdTriList]
  | cons a l =>
    cases l with
    | nil => simp [decodeOrdTriList]
    | cons b l =>
      cases l with
      | nil => simp [decodeOrdTriList]
      | cons c l =>
        cases l with
        | cons d l => simp [decodeOrdTriList]
        | nil =>
          have habc : a ≤ b ∧ b ≤ c := by simpa [List.isChain_cons] using hl
          rw (config := { transparency := .default }) [decodeOrdTriList, dif_pos habc, orderCellSingularChain2_single]
          apply single_mem_subChains
          intro z
          apply orderNerveSingularSimplex_supported
          intro i
          fin_cases i
          · exact hv a (by simp)
          · exact hv b (by simp)
          · exact hv c (by simp)

/-- Realizing an increasing two-chain preserves every vertex carrier. -/
theorem orderCellSingularDecode2_supported {P : Type} [PartialOrder P]
    (A : Set P) {c : Nerve.Ch P} (hc : c ∈ Nerve.IncOn A) :
    orderCellSingularChain2 (decodeOrdNerve2 c) ∈
      subChains (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) 2 := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, hl, rfl⟩
    rw (config := { transparency := .default }) [decodeOrdNerve2_of]
    exact orderCellSingularDecode2List_supported A l hl.1 hl.2
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | neg x _ hx => simpa only [map_neg] using Submodule.neg_mem _ hx

end FiniteChains.Comb
