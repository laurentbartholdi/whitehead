module

public import RequestProject.OrderThreeNormalization

@[expose] public section

/-! Normalization preserves the actual vertex tuples in the support of finite chains. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

theorem normalizeOrdChain2_support (z : OrdTri P →₀ ℤ) (t : StrictOrdTri P)
    (ht : t ∈ (normalizeOrdChain2 z).support) :
    ∃ a ∈ z.support, a.1 = t.1 := by
  classical
  change t ∈ (∑ a ∈ z.support, z a • normalizeOrdTriangle a).support at ht
  obtain ⟨a, ha, hta⟩ := Finsupp.mem_support_finset_sum t ht
  have hn : normalizeOrdTriangle a t ≠ 0 := by
    intro he
    have h := Finsupp.mem_support_iff.mp hta
    rw [Finsupp.smul_apply, he, smul_zero] at h
    exact h rfl
  unfold normalizeOrdTriangle at hn
  split_ifs at hn with h
  · have he : (⟨a.1, h⟩ : StrictOrdTri P) = t := by
      by_contra hne
      exact hn (by simp [hne])
    exact ⟨a, ha, congrArg Subtype.val he⟩
  · simp at hn

end FiniteChains.Comb
