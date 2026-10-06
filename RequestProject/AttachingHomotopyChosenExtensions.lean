import RequestProject.AttachingHomotopyEquiv

/-! The attaching equivalence with specified extensions. This permits a
natural explicit extension to replace unrelated choices of HEP witnesses.
Both inverse homotopies remain the actual backtrack construction. Unverified. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical ContinuousMap
universe u
variable {D P : Type u} [TopologicalSpace D] [TopologicalSpace P]
  (S : Set D) (a₀ a₁ : C(S, P)) (H : a₀.Homotopy a₁)
  (L₀ : C(I × D, Space a₀ Subtype.val))
  (L₁ : C(I × D, Space a₁ Subtype.val))
  (h₀ : ∀ d, L₀ (0, d) = cell a₀ Subtype.val d)
  (h₁ : ∀ d, L₁ (0, d) = cell a₁ Subtype.val d)
  (hs₀ : ∀ t a, L₀ (t, a.val) = old a₀ Subtype.val (H (t, a)))
  (hs₁ : ∀ t a, L₁ (t, a.val) = old a₁ Subtype.val (H.symm (t, a)))

def chosenAttachingBackward : C(Space a₁ Subtype.val, Space a₀ Subtype.val) :=
  desc a₁ Subtype.val ⟨old a₀ Subtype.val, old_continuous _ _⟩
    (L₀.comp ⟨fun d => (1, d), continuous_const.prodMk continuous_id⟩)
    (fun a => by
      change old a₀ Subtype.val (a₁ a) = L₀ (1, a.val)
      rw [hs₀, H.apply_one])

def chosenAttachingForward : C(Space a₀ Subtype.val, Space a₁ Subtype.val) :=
  desc a₀ Subtype.val ⟨old a₁ Subtype.val, old_continuous _ _⟩
    (L₁.comp ⟨fun d => (1, d), continuous_const.prodMk continuous_id⟩)
    (fun a => by
      change old a₁ Subtype.val (a₀ a) = L₁ (1, a.val)
      rw [hs₁, H.symm.apply_one])

@[simp] theorem chosenAttachingBackward_cell (d : D) :
    chosenAttachingBackward S a₀ a₁ H L₀ hs₀ (cell a₁ Subtype.val d) = L₀ (1, d) := by
  unfold chosenAttachingBackward
  rw [desc_cell]
  rfl

@[simp] theorem chosenAttachingForward_cell (d : D) :
    chosenAttachingForward S a₀ a₁ H L₁ hs₁ (cell a₀ Subtype.val d) = L₁ (1, d) := by
  unfold chosenAttachingForward
  rw [desc_cell]
  rfl

def attachingHomotopyEquivOfExtensions (hS : IsClosed S)
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D)) :
    Space a₀ Subtype.val ≃ₕ Space a₁ Subtype.val where
  toFun := chosenAttachingForward S a₀ a₁ H L₁ hs₁
  invFun := chosenAttachingBackward S a₀ a₁ H L₀ hs₀
  left_inv := attachingBacktrack_homotopic_id S hS hfull a₀ a₁ H _ _
    (fun _ => rfl) (fun _ => rfl) L₀ L₁ h₀ h₁ hs₀ hs₁
    (chosenAttachingBackward_cell S a₀ a₁ H L₀ hs₀)
    (chosenAttachingForward_cell S a₀ a₁ H L₁ hs₁)
  right_inv := by
    apply attachingBacktrack_homotopic_id S hS hfull a₁ a₀ H.symm _ _
      (fun _ => rfl) (fun _ => rfl) L₁ L₀ h₁ h₀ hs₁ _
      (chosenAttachingForward_cell S a₀ a₁ H L₁ hs₁)
      (chosenAttachingBackward_cell S a₀ a₁ H L₀ hs₀)
    intro t a
    simpa only [ContinuousMap.Homotopy.symm_symm] using hs₀ t a

end FiniteChains.RelativeAttachment
