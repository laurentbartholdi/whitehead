import RequestProject.AttachmentHomotopyExtension

/-! Continuous pasting on the two ends and the side of a cylinder.
The side is any closed subspace, including an arbitrary disjoint family of
disk boundaries. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u v
variable {D : Type u} [TopologicalSpace D] (S : Set D)

abbrev FullCylinderBoundary :=
  {z : I × D // z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ S}

variable {Z : Type v} [TopologicalSpace Z]

private def fullCylinderPastingFun (f₀ f₁ : C(D, Z)) (H : C(I × S, Z))
    (z : FullCylinderBoundary S) : Z :=
  if h₀ : z.val.1 = 0 then f₀ z.val.2
  else if h₁ : z.val.1 = 1 then f₁ z.val.2
  else H (z.val.1, ⟨z.val.2, (z.property.resolve_left h₀).resolve_left h₁⟩)

private theorem fullCylinderPastingFun_zero (f₀ f₁ : C(D, Z)) (H : C(I × S, Z))
    (z : FullCylinderBoundary S) (hz : z.val.1 = 0) :
    fullCylinderPastingFun S f₀ f₁ H z = f₀ z.val.2 := by
  simp only [fullCylinderPastingFun, dif_pos hz]

private theorem fullCylinderPastingFun_one (f₀ f₁ : C(D, Z)) (H : C(I × S, Z))
    (z : FullCylinderBoundary S) (hz : z.val.1 = 1) :
    fullCylinderPastingFun S f₀ f₁ H z = f₁ z.val.2 := by
  have hzero : z.val.1 ≠ 0 := by rw [hz]; exact one_ne_zero
  simp only [fullCylinderPastingFun, dif_neg hzero, dif_pos hz]

private theorem fullCylinderPastingFun_side (f₀ f₁ : C(D, Z)) (H : C(I × S, Z))
    (h₀ : ∀ x, H (0, x) = f₀ x.val) (h₁ : ∀ x, H (1, x) = f₁ x.val)
    (z : FullCylinderBoundary S) (hz : z.val.2 ∈ S) :
    fullCylinderPastingFun S f₀ f₁ H z = H (z.val.1, ⟨z.val.2, hz⟩) := by
  by_cases ht₀ : z.val.1 = 0
  · rw [fullCylinderPastingFun_zero S f₀ f₁ H z ht₀, ht₀, h₀]
  by_cases ht₁ : z.val.1 = 1
  · rw [fullCylinderPastingFun_one S f₀ f₁ H z ht₁, ht₁, h₁]
  simp only [fullCylinderPastingFun, dif_neg ht₀, dif_neg ht₁]

/-- Pasting on the full cylinder boundary, with exact formulas on each of
the three closed pieces. -/
def fullCylinderPasting (hS : IsClosed S) (f₀ f₁ : C(D, Z)) (H : C(I × S, Z))
    (h₀ : ∀ x, H (0, x) = f₀ x.val) (h₁ : ∀ x, H (1, x) = f₁ x.val) :
    C(FullCylinderBoundary S, Z) where
  toFun := fullCylinderPastingFun S f₀ f₁ H
  continuous_toFun := by
    let B₀ : Set (FullCylinderBoundary S) := {z | z.val.1 = 0}
    let B₁ : Set (FullCylinderBoundary S) := {z | z.val.1 = 1}
    let C : Set (FullCylinderBoundary S) := {z | z.val.2 ∈ S}
    have hb₀ : IsClosed B₀ := isClosed_eq (by fun_prop) continuous_const
    have hb₁ : IsClosed B₁ := isClosed_eq (by fun_prop) continuous_const
    have hc : IsClosed C := hS.preimage (continuous_snd.comp continuous_subtype_val)
    have hcover : (B₀ ∪ B₁) ∪ C = Set.univ := by
      apply Set.eq_univ_of_forall
      intro z
      rcases z.property with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    have hf₀ : ContinuousOn (fullCylinderPastingFun S f₀ f₁ H) B₀ := by
      apply ((f₀.continuous.comp (continuous_snd.comp continuous_subtype_val)).continuousOn).congr
      exact fun z hz => fullCylinderPastingFun_zero S f₀ f₁ H z hz
    have hf₁ : ContinuousOn (fullCylinderPastingFun S f₀ f₁ H) B₁ := by
      apply ((f₁.continuous.comp (continuous_snd.comp continuous_subtype_val)).continuousOn).congr
      exact fun z hz => fullCylinderPastingFun_one S f₀ f₁ H z hz
    have hh : ContinuousOn (fullCylinderPastingFun S f₀ f₁ H) C := by
      rw [continuousOn_iff_continuous_restrict]
      let k : C(C, I × S) := {
        toFun := fun z => (z.val.val.1, ⟨z.val.val.2, z.property⟩)
        continuous_toFun := by fun_prop }
      have he : C.domRestrict (fullCylinderPastingFun S f₀ f₁ H) = H ∘ k := by
        funext z
        exact fullCylinderPastingFun_side S f₀ f₁ H h₀ h₁ z.val z.property
      rw [he]
      exact H.continuous.comp k.continuous
    rw [← continuousOn_univ, ← hcover]
    exact (hf₀.union_of_isClosed hf₁ hb₀ hb₁).union_of_isClosed hh (hb₀.union hb₁) hc

@[simp] theorem fullCylinderPasting_zero (hS : IsClosed S) (f₀ f₁ : C(D, Z))
    (H : C(I × S, Z)) (h₀ : ∀ x, H (0, x) = f₀ x.val)
    (h₁ : ∀ x, H (1, x) = f₁ x.val) (d : D) :
    fullCylinderPasting S hS f₀ f₁ H h₀ h₁ ⟨(0, d), Or.inl rfl⟩ = f₀ d :=
  fullCylinderPastingFun_zero S f₀ f₁ H _ rfl

@[simp] theorem fullCylinderPasting_one (hS : IsClosed S) (f₀ f₁ : C(D, Z))
    (H : C(I × S, Z)) (h₀ : ∀ x, H (0, x) = f₀ x.val)
    (h₁ : ∀ x, H (1, x) = f₁ x.val) (d : D) :
    fullCylinderPasting S hS f₀ f₁ H h₀ h₁ ⟨(1, d), Or.inr (Or.inl rfl)⟩ = f₁ d :=
  fullCylinderPastingFun_one S f₀ f₁ H _ rfl

@[simp] theorem fullCylinderPasting_side (hS : IsClosed S) (f₀ f₁ : C(D, Z))
    (H : C(I × S, Z)) (h₀ : ∀ x, H (0, x) = f₀ x.val)
    (h₁ : ∀ x, H (1, x) = f₁ x.val) (t : I) (x : S) :
    fullCylinderPasting S hS f₀ f₁ H h₀ h₁
      ⟨(t, x.val), Or.inr (Or.inr x.property)⟩ = H (t, x) :=
  fullCylinderPastingFun_side S f₀ f₁ H h₀ h₁ _ x.property

end FiniteChains.RelativeAttachment
