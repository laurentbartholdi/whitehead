module

public import RequestProject.StrictOrderChains

@[expose] public section

/-! Finite cycle decomposition by labels constant on actual comparable vertices. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open scoped Classical
universe u v
variable {P : Type u} [PartialOrder P] {I : Type v}
  (label : P → I) (hlabel : ∀ {a b : P}, a ≤ b → label a = label b)

include hlabel in
theorem strict_label_boundary (i : I) (c : StrictOrdTri P →₀ ℤ) :
    FiniteChains.Comb.bdry2 (strictOrderCx P) (c.filter (fun t => label t.1.1 = i)) =
      (FiniteChains.Comb.bdry2 (strictOrderCx P) c).filter (fun e => label e.1.1 = i) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [Finsupp.filter_zero, map_zero]
  | add c d hc hd => rw [Finsupp.filter_add, map_add, hc, hd, map_add, Finsupp.filter_add]
  | single t n =>
    have hab : label t.1.1 = label t.1.2.1 := hlabel t.2.1.le
    by_cases hi : label t.1.1 = i
    · have hbi : label t.1.2.1 = i := hab.symm.trans hi
      simp [Finsupp.filter_single_of_pos, hi, hbi, Comb.bdry2, strictOrderCx,
        pathChain, Finsupp.linearCombination_apply, Finsupp.filter_add]
    · have hbi : label t.1.2.1 ≠ i := fun h => hi (hab.trans h)
      simp [Finsupp.filter_single_of_neg, hi, hbi, Comb.bdry2, strictOrderCx,
        pathChain, Finsupp.linearCombination_apply, Finsupp.filter_add]

include hlabel in
theorem strict_label_cycle (i : I) (c : StrictOrdTri P →₀ ℤ)
    (hc : FiniteChains.Comb.bdry2 (strictOrderCx P) c = 0) :
    FiniteChains.Comb.bdry2 (strictOrderCx P) (c.filter (fun t => label t.1.1 = i)) = 0 := by
  rw [strict_label_boundary label hlabel, hc, Finsupp.filter_zero]

theorem strict_chain_sum_labels (c : StrictOrdTri P →₀ ℤ) :
    ∑ i ∈ c.support.image (fun t => label t.1.1),
      c.filter (fun t => label t.1.1 = i) = c := by
  ext t
  by_cases ht : c t = 0
  · simp [Finsupp.filter_apply, ht]
  · have hm : label t.1.1 ∈ c.support.image (fun t => label t.1.1) :=
      Finset.mem_image.mpr ⟨t, Finsupp.mem_support_iff.mpr ht, rfl⟩
    simp only [Finsupp.finset_sum_apply, Finsupp.filter_apply]
    rw [Finset.sum_eq_single (label t.1.1)]
    · simp
    · intro i _ hi
      simp [Ne.symm hi]
    · exact fun h => False.elim (h hm)

include hlabel in
theorem strict_label_filter_support (i : I) (c : StrictOrdTri P →₀ ℤ)
    (t : StrictOrdTri P) (ht : t ∈ (c.filter (fun t => label t.1.1 = i)).support) :
    label t.1.1 = i ∧ label t.1.2.1 = i ∧ label t.1.2.2 = i := by
  have hi : label t.1.1 = i := by
    by_contra hn
    have hzero : (c.filter (fun t => label t.1.1 = i)) t = 0 := by
      simp [hn]
    exact (Finsupp.mem_support_iff.mp ht) hzero
  exact ⟨hi, (hlabel t.2.1.le).symm.trans hi,
    (hlabel (t.2.1.trans t.2.2).le).symm.trans hi⟩

include hlabel in
theorem exists_strict_label_cycle_decomposition (c : StrictOrdTri P →₀ ℤ)
    (hc : FiniteChains.Comb.bdry2 (strictOrderCx P) c = 0) :
    ∃ (s : Finset I) (d : I → (StrictOrdTri P →₀ ℤ)),
      (∀ i, FiniteChains.Comb.bdry2 (strictOrderCx P) (d i) = 0) ∧
      (∀ i t, t ∈ (d i).support → label t.1.1 = i ∧
        label t.1.2.1 = i ∧ label t.1.2.2 = i) ∧ c = ∑ i ∈ s, d i := by
  refine ⟨c.support.image (fun t => label t.1.1),
    fun i => c.filter (fun t => label t.1.1 = i),
    fun i => strict_label_cycle label hlabel i c hc,
    fun i t ht => strict_label_filter_support label hlabel i c t ht, ?_⟩
  exact (strict_chain_sum_labels label c).symm

end FiniteChains.Comb
