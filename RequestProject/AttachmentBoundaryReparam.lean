import RequestProject.ExplicitRelativeAttachment

/-! Reparametrizing the boundary changes neither the literal old points
nor the attached disk points, and gives a genuine homeomorphism. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open scoped Classical

universe u
variable {A D P : Type u} [TopologicalSpace A] [TopologicalSpace D] [TopologicalSpace P]

def attachmentBoundaryReparamForward (a : A → P) (i : A → D) (S : Set D)
    (b : A ≃ₜ S) (hb : ∀ x, (b x).val = i x) :
    C(Space a i, Space (a ∘ b.symm) Subtype.val) :=
  desc a i ⟨old (a ∘ b.symm) Subtype.val, old_continuous _ _⟩
    ⟨cell (a ∘ b.symm) Subtype.val, cell_continuous _ _⟩ (fun x => by
      change old (a ∘ b.symm) Subtype.val (a x) = cell (a ∘ b.symm) Subtype.val (i x)
      rw [← hb x, cell_boundary _ Subtype.val Subtype.val_injective]
      exact congrArg (old (a ∘ b.symm) Subtype.val)
        (congrArg a (b.symm_apply_apply x)).symm)

def attachmentBoundaryReparamBackward (a : A → P) (i : A → D)
    (hi : Function.Injective i) (S : Set D)
    (b : A ≃ₜ S) (hb : ∀ x, (b x).val = i x) :
    C(Space (a ∘ b.symm) Subtype.val, Space a i) :=
  desc (a ∘ b.symm) Subtype.val ⟨old a i, old_continuous _ _⟩
    ⟨cell a i, cell_continuous _ _⟩ (fun x => by
      change old a i (a (b.symm x)) = cell a i x.val
      have hx : i (b.symm x) = x.val :=
        (hb (b.symm x)).symm.trans (congrArg Subtype.val (b.apply_symm_apply x))
      rw [← hx, cell_boundary a i hi])

def attachmentBoundaryReparam (a : A → P) (i : A → D)
    (hi : Function.Injective i) (S : Set D)
    (b : A ≃ₜ S) (hb : ∀ x, (b x).val = i x) :
    Space a i ≃ₜ Space (a ∘ b.symm) Subtype.val where
  toFun := attachmentBoundaryReparamForward a i S b hb
  invFun := attachmentBoundaryReparamBackward a i hi S b hb
  left_inv z := by
    obtain ⟨w, rfl⟩ := quotientMap_surjective a i z
    cases w with
    | inl p => rfl
    | inr d =>
      change desc _ _ _ _ _ (desc _ _ _ _ _ (cell a i d)) = cell a i d
      simp only [desc_cell, ContinuousMap.coe_mk]
  right_inv z := by
    obtain ⟨w, rfl⟩ := quotientMap_surjective (a ∘ b.symm) Subtype.val z
    cases w with
    | inl p => rfl
    | inr d =>
      change desc _ _ _ _ _ (desc _ _ _ _ _ (cell (a ∘ b.symm) Subtype.val d)) = _
      simp only [desc_cell, ContinuousMap.coe_mk]
      rfl
  continuous_toFun := (attachmentBoundaryReparamForward a i S b hb).continuous
  continuous_invFun := (attachmentBoundaryReparamBackward a i hi S b hb).continuous

@[simp] theorem attachmentBoundaryReparam_old (a : A → P) (i : A → D)
    (hi : Function.Injective i) (S : Set D)
    (b : A ≃ₜ S) (hb : ∀ x, (b x).val = i x) (p : P) :
    attachmentBoundaryReparam a i hi S b hb (old a i p) =
      old (a ∘ b.symm) Subtype.val p := rfl

@[simp] theorem attachmentBoundaryReparam_cell (a : A → P) (i : A → D)
    (hi : Function.Injective i) (S : Set D)
    (b : A ≃ₜ S) (hb : ∀ x, (b x).val = i x) (d : D) :
    attachmentBoundaryReparam a i hi S b hb (cell a i d) =
      cell (a ∘ b.symm) Subtype.val d := by
  change attachmentBoundaryReparamForward a i S b hb (cell a i d) = _
  unfold attachmentBoundaryReparamForward
  rw [desc_cell]
  rfl

@[simp] theorem attachmentBoundaryReparam_symm_old (a : A → P) (i : A → D)
    (hi : Function.Injective i) (S : Set D)
    (b : A ≃ₜ S) (hb : ∀ x, (b x).val = i x) (p : P) :
    (attachmentBoundaryReparam a i hi S b hb).symm (old (a ∘ b.symm) Subtype.val p) =
      old a i p := rfl

@[simp] theorem attachmentBoundaryReparam_symm_cell (a : A → P) (i : A → D)
    (hi : Function.Injective i) (S : Set D)
    (b : A ≃ₜ S) (hb : ∀ x, (b x).val = i x) (d : D) :
    (attachmentBoundaryReparam a i hi S b hb).symm (cell (a ∘ b.symm) Subtype.val d) =
      cell a i d := by
  change attachmentBoundaryReparamBackward a i hi S b hb
    (cell (a ∘ b.symm) Subtype.val d) = _
  unfold attachmentBoundaryReparamBackward
  rw [desc_cell]
  rfl

end FiniteChains.RelativeAttachment
