module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.AttachmentBacktrackHomotopy

@[expose] public section

/-! Homotopic attaching maps have homotopy equivalent attachment spaces.
The equivalence is the identity on the literal old summand. The inverse
and both homotopies are constructed using disk and cylinder extension. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u
variable {D P : Type u} [TopologicalSpace D] [TopologicalSpace P]

theorem exists_attachingDiskExtension (S : Set D)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (a₀ a₁ : C(S, P)) (H : a₀.Homotopy a₁) :
    ∃ L : C(I × D, Space a₀ Subtype.val),
      (∀ d, L (0, d) = cell a₀ Subtype.val d) ∧
      ∀ t a, L (t, a.val) = old a₀ Subtype.val (H (t, a)) := by
  apply hext (Space a₀ Subtype.val)
    ⟨cell a₀ Subtype.val, cell_continuous _ _⟩
    ((⟨old a₀ Subtype.val, old_continuous _ _⟩ : C(P, Space a₀ Subtype.val)).comp
      H.toContinuousMap)
  intro a
  change old a₀ Subtype.val (H (0, a)) = cell a₀ Subtype.val a.val
  rw [H.apply_zero]
  exact (cell_boundary a₀ Subtype.val Subtype.val_injective a).symm

def attachingDiskExtension (S : Set D)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (a₀ a₁ : C(S, P)) (H : a₀.Homotopy a₁) : C(I × D, Space a₀ Subtype.val) :=
  Classical.choose (exists_attachingDiskExtension S hext a₀ a₁ H)

theorem attachingDiskExtension_zero (S : Set D)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (a₀ a₁ : C(S, P)) (H : a₀.Homotopy a₁) (d : D) :
    attachingDiskExtension S hext a₀ a₁ H (0, d) = cell a₀ Subtype.val d :=
  (Classical.choose_spec (exists_attachingDiskExtension S hext a₀ a₁ H)).1 d

theorem attachingDiskExtension_side (S : Set D)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (a₀ a₁ : C(S, P)) (H : a₀.Homotopy a₁) (t : I) (a : S) :
    attachingDiskExtension S hext a₀ a₁ H (t, a.val) = old a₀ Subtype.val (H (t, a)) :=
  (Classical.choose_spec (exists_attachingDiskExtension S hext a₀ a₁ H)).2 t a

def attachingBackwardMap (S : Set D)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (a₀ a₁ : C(S, P)) (H : a₀.Homotopy a₁) :
    C(Space a₁ Subtype.val, Space a₀ Subtype.val) :=
  desc a₁ Subtype.val ⟨old a₀ Subtype.val, old_continuous _ _⟩
    ((attachingDiskExtension S hext a₀ a₁ H).comp
      ⟨fun d => (1, d), continuous_const.prodMk continuous_id⟩)
    (fun a => by
      change old a₀ Subtype.val (a₁ a) = attachingDiskExtension S hext a₀ a₁ H (1, a.val)
      rw [attachingDiskExtension_side, H.apply_one])

@[simp] theorem attachingBackwardMap_old (S : Set D)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (a₀ a₁ : C(S, P)) (H : a₀.Homotopy a₁) (p : P) :
    attachingBackwardMap S hext a₀ a₁ H (old a₁ Subtype.val p) = old a₀ Subtype.val p := rfl

@[simp] theorem attachingBackwardMap_cell (S : Set D)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (a₀ a₁ : C(S, P)) (H : a₀.Homotopy a₁) (d : D) :
    attachingBackwardMap S hext a₀ a₁ H (cell a₁ Subtype.val d) =
      attachingDiskExtension S hext a₀ a₁ H (1, d) := by
  unfold attachingBackwardMap
  rw [desc_cell]
  rfl

def attachingHomotopyEquiv (S : Set D) (hS : IsClosed S)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D))
    (a₀ a₁ : C(S, P)) (H : a₀.Homotopy a₁) :
    ContinuousMap.HomotopyEquiv (Space a₀ Subtype.val) (Space a₁ Subtype.val) where
  toFun := attachingBackwardMap S hext a₁ a₀ H.symm
  invFun := attachingBackwardMap S hext a₀ a₁ H
  left_inv := attachingBacktrack_homotopic_id S hS hfull a₀ a₁ H _ _
    (attachingBackwardMap_old S hext a₀ a₁ H)
    (attachingBackwardMap_old S hext a₁ a₀ H.symm)
    (attachingDiskExtension S hext a₀ a₁ H)
    (attachingDiskExtension S hext a₁ a₀ H.symm)
    (attachingDiskExtension_zero S hext a₀ a₁ H)
    (attachingDiskExtension_zero S hext a₁ a₀ H.symm)
    (attachingDiskExtension_side S hext a₀ a₁ H)
    (attachingDiskExtension_side S hext a₁ a₀ H.symm)
    (attachingBackwardMap_cell S hext a₀ a₁ H)
    (attachingBackwardMap_cell S hext a₁ a₀ H.symm)
  right_inv := by
    apply attachingBacktrack_homotopic_id S hS hfull a₁ a₀ H.symm _ _
      (attachingBackwardMap_old S hext a₁ a₀ H.symm)
      (attachingBackwardMap_old S hext a₀ a₁ H)
      (attachingDiskExtension S hext a₁ a₀ H.symm)
      (attachingDiskExtension S hext a₀ a₁ H)
      (attachingDiskExtension_zero S hext a₁ a₀ H.symm)
      (attachingDiskExtension_zero S hext a₀ a₁ H)
      (attachingDiskExtension_side S hext a₁ a₀ H.symm) _
      (attachingBackwardMap_cell S hext a₁ a₀ H.symm)
      (attachingBackwardMap_cell S hext a₀ a₁ H)
    intro t a
    simpa only [ContinuousMap.Homotopy.symm_symm] using
      attachingDiskExtension_side S hext a₀ a₁ H t a

end FiniteChains.RelativeAttachment
