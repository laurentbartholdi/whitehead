import RequestProject.AttachingHomotopyEquiv
import RequestProject.HomotopyEquivCancellation

/-! Homotopy invariance of actual cell attachments under change of their
base. Both required homotopy extension properties are supplied for disks
by the explicit ball constructions. No equivalence of the pushout is
assumed in the conclusion's construction. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u
variable {D P K : Type u} [TopologicalSpace D] [TopologicalSpace P] [TopologicalSpace K]

def attachmentBaseMapEquivOfHomotopicId (S : Set D) (hS : IsClosed S)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D))
    (a : C(S, P)) (h : C(P, P))
    (H : ContinuousMap.Homotopy (ContinuousMap.id P) h) :
    ContinuousMap.HomotopyEquiv (Space a Subtype.val) (Space (h ∘ a) Subtype.val) := by
  let Hatt : a.Homotopy (h.comp a) := H.compContinuousMap a
  let C := (attachingHomotopyEquiv S hS hext hfull a (h.comp a) Hatt).symm
  let F := attachmentBaseMap a Subtype.val Subtype.val_injective h
  let L := attachingDiskExtension S hext a (h.comp a) Hatt
  let HOld : C(I × P, Space a Subtype.val) :=
    ⟨fun tp => old a Subtype.val (H tp), (old_continuous _ _).comp H.continuous⟩
  have hcompat : ∀ t b, HOld (t, a b) = L (t, b.val) := by
    intro t b
    exact (attachingDiskExtension_side S hext a (h.comp a) Hatt t b).symm
  let T := attachmentHomotopyPasting a Subtype.val HOld L hcompat
  have HT : ContinuousMap.Homotopy (ContinuousMap.id (Space a Subtype.val))
      (C.toFun.comp F) := {
    toContinuousMap := T
    map_zero_left := by
      intro z
      obtain ⟨w, rfl⟩ := quotientMap_surjective a Subtype.val z
      cases w with
      | inl p => exact congrArg (old a Subtype.val) (H.apply_zero p)
      | inr d =>
        exact (attachmentHomotopyPasting_cell a Subtype.val HOld L hcompat 0 d).trans
          (attachingDiskExtension_zero S hext a (h.comp a) Hatt d)
    map_one_left := by
      intro z
      obtain ⟨w, rfl⟩ := quotientMap_surjective a Subtype.val z
      cases w with
      | inl p =>
        change old a Subtype.val (H (1, p)) = old a Subtype.val (h p)
        exact congrArg (old a Subtype.val) (H.apply_one p)
      | inr d =>
        change T (1, cell a Subtype.val d) =
          attachingBackwardMap S hext a (h.comp a) Hatt (F (cell a Subtype.val d))
        rw [attachmentHomotopyPasting_cell, attachmentBaseMap_cell]
        exact (attachingBackwardMap_cell S hext a (h.comp a) Hatt d).symm }
  exact ContinuousMap.HomotopyEquiv.ofHomotopicSection C F ⟨HT.symm⟩

@[simp] theorem attachmentBaseMapEquivOfHomotopicId_toFun (S : Set D) (hS : IsClosed S)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D))
    (a : C(S, P)) (h : C(P, P))
    (H : ContinuousMap.Homotopy (ContinuousMap.id P) h) :
    (attachmentBaseMapEquivOfHomotopicId S hS hext hfull a h H).toFun =
      attachmentBaseMap a Subtype.val Subtype.val_injective h := rfl

/-- Change of the base by an actual homotopy equivalence induces an actual
homotopy equivalence on the attached spaces. Its forward map is precisely
the universal pushout map extending the original base map and disk maps. -/
def attachmentBaseChangeHomotopyEquiv (S : Set D) (hS : IsClosed S)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D))
    (a : C(S, P)) (e : ContinuousMap.HomotopyEquiv P K) :
    ContinuousMap.HomotopyEquiv (Space a Subtype.val) (Space (e.toFun ∘ a) Subtype.val) := by
  let f := attachmentBaseMap a Subtype.val Subtype.val_injective e.toFun
  let g := attachmentBaseMap (e.toFun ∘ a) Subtype.val Subtype.val_injective e.invFun
  let h := attachmentBaseMap (e.invFun ∘ e.toFun ∘ a) Subtype.val
    Subtype.val_injective e.toFun
  let E := attachmentBaseMapEquivOfHomotopicId S hS hext hfull a
    (e.invFun.comp e.toFun) (Classical.choice e.left_inv).symm
  let D := attachmentBaseMapEquivOfHomotopicId S hS hext hfull (e.toFun.comp a)
    (e.toFun.comp e.invFun) (Classical.choice e.right_inv).symm
  have hE : E.toFun = g.comp f :=
    (attachmentBaseMap_comp a Subtype.val Subtype.val_injective e.toFun e.invFun).symm
  have hD : D.toFun = h.comp g :=
    (attachmentBaseMap_comp (e.toFun ∘ a) Subtype.val
      Subtype.val_injective e.invFun e.toFun).symm
  exact ContinuousMap.HomotopyEquiv.twoOfSixLeft f g h E hE D hD

@[simp] theorem attachmentBaseChangeHomotopyEquiv_toFun (S : Set D) (hS : IsClosed S)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D))
    (a : C(S, P)) (e : ContinuousMap.HomotopyEquiv P K) :
    (attachmentBaseChangeHomotopyEquiv S hS hext hfull a e).toFun =
      attachmentBaseMap a Subtype.val Subtype.val_injective e.toFun := rfl

@[simp] theorem attachmentBaseChangeHomotopyEquiv_old (S : Set D) (hS : IsClosed S)
    (hext : HasHomotopyExtension (Subtype.val : S → D))
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D))
    (a : C(S, P)) (e : ContinuousMap.HomotopyEquiv P K) (p : P) :
    attachmentBaseChangeHomotopyEquiv S hS hext hfull a e (old a Subtype.val p) =
      old (e.toFun ∘ a) Subtype.val (e p) := rfl

end FiniteChains.RelativeAttachment
