module

public import RequestProject.CellComplex

@[expose] public section

/-! A finitely supported chain can be split by incidence labels.  The
boundary identity below requires homogeneity only at cells in its actual
support.  Thus it applies to a union of components inside a larger complex.
Unverified source. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Comb
universe u v w

theorem finsupp_filter_of_constant_label {I : Type u} {J : Type v}
    (label : I → J) (j : J) (c : I →₀ ℤ) (k : J)
    (hc : ∀ i, c i ≠ 0 → label i = j) :
    c.filter (fun i => label i = k) = if j = k then c else 0 := by
  ext i
  by_cases hjk : j = k
  · subst k
    rw [if_pos rfl]
    by_cases hi : c i = 0
    · simp [Finsupp.filter_apply, hi]
    · simp [hc i hi]
  · rw [if_neg hjk]
    by_cases hi : c i = 0
    · simp [Finsupp.filter_apply, hi]
    · simp [hc i hi, hjk]

theorem supported_label_boundary {I : Type u} {J : Type v} {T : Type w}
    (d : (I →₀ ℤ) →ₗ[ℤ] (J →₀ ℤ)) (labelI : I → T) (labelJ : J → T)
    (old : I → Prop)
    (hd : ∀ i, old i → ∀ j, d (Finsupp.single i 1) j ≠ 0 → labelJ j = labelI i)
    (c : I →₀ ℤ) (hc : ∀ i ∈ c.support, old i) (k : T) :
    d (c.filter (fun i => labelI i = k)) = (d c).filter (fun j => labelJ j = k) := by
  have hs (i : I) (hi : i ∈ c.support) :
      d ((Finsupp.single i (c i)).filter (fun i => labelI i = k)) =
        (d (Finsupp.single i (c i))).filter (fun j => labelJ j = k) := by
    have hm : ∀ j, d (Finsupp.single i (c i)) j ≠ 0 → labelJ j = labelI i := by
      intro j hj
      apply hd i (hc i hi) j
      intro hz
      apply hj
      have hsingle : Finsupp.single i (c i) = (c i) • Finsupp.single i (1 : ℤ) := by simp
      rw [hsingle, map_smul]
      simp [hz]
    rw [finsupp_filter_of_constant_label labelJ (labelI i) _ k hm]
    by_cases hik : labelI i = k
    · rw [Finsupp.filter_single_of_pos (fun i => labelI i = k) hik, if_pos hik]
    · rw [Finsupp.filter_single_of_neg (fun i => labelI i = k) hik, if_neg hik, map_zero]
  calc
    d (c.filter (fun i => labelI i = k)) =
        d ((∑ i ∈ c.support, Finsupp.single i (c i)).filter (fun i => labelI i = k)) := by
          rw [show (∑ i ∈ c.support, Finsupp.single i (c i)) = c from c.sum_single]
    _ = ∑ i ∈ c.support,
        d ((Finsupp.single i (c i)).filter (fun i => labelI i = k)) := by
          rw [Finsupp.filter_sum, map_sum]
    _ = ∑ i ∈ c.support,
        (d (Finsupp.single i (c i))).filter (fun j => labelJ j = k) :=
          Finset.sum_congr rfl hs
    _ = (d c).filter (fun j => labelJ j = k) := by
          rw [← Finsupp.filter_sum, ← map_sum]
          rw [show (∑ i ∈ c.support, Finsupp.single i (c i)) = c from c.sum_single]

theorem finsupp_sum_label_filters {I : Type u} {J : Type v}
    (label : I → J) (c : I →₀ ℤ) :
    ∑ j ∈ c.support.image label, c.filter (fun i => label i = j) = c := by
  ext i
  by_cases hi : c i = 0
  · simp [Finsupp.filter_apply, hi]
  · have hm : label i ∈ c.support.image label :=
      Finset.mem_image.mpr ⟨i, Finsupp.mem_support_iff.mpr hi, rfl⟩
    simp only [Finsupp.finset_sum_apply, Finsupp.filter_apply]
    rw [Finset.sum_eq_single (label i)]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · exact fun h => False.elim (h hm)

end FiniteChains.Comb
