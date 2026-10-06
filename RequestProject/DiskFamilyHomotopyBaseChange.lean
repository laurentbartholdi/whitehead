module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.ClassicalCellAttachmentMaps
public import RequestProject.SigmaCylinderHomotopyExtension
public import RequestProject.AttachmentBoundaryReparam
public import RequestProject.AttachmentHomotopyBaseChange
public import RequestProject.TopologicalPi2HomotopyTransport

@[expose] public section

/-! Homotopy invariance for arbitrary families of actual disk attachments.
All extension inputs are discharged by the explicit ball/cylinder maps.
The forward map retains the disk labels and is the given map on old points. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u
variable (J E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

def diskFamilyBoundarySet : Set (DiskFamily J E) :=
  SigmaSubspace (fun _ : J => {d : ClosedUnitBall E | ‖d.val‖ = 1})

omit [NormedSpace ℝ E] in
theorem diskFamilyBoundarySet_isClosed : IsClosed (diskFamilyBoundarySet J E) :=
  sigmaSubspace_isClosed _ (fun _ =>
    isClosed_eq (continuous_norm.comp continuous_subtype_val) continuous_const)

omit [NormedSpace ℝ E] in
theorem boundaryFamilyInclusion_range_eq :
    Set.range (boundaryFamilyInclusion J E) = diskFamilyBoundarySet J E := by
  ext d
  exact boundaryFamilyInclusion_range J E d

def diskFamilyBoundaryHomeomorph : BoundaryFamily J E ≃ₜ diskFamilyBoundarySet J E :=
  (boundaryFamilyInclusion_isClosedEmbedding J E).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (boundaryFamilyInclusion_range_eq J E))

omit [NormedSpace ℝ E] in
@[simp] theorem diskFamilyBoundaryHomeomorph_val (a : BoundaryFamily J E) :
    (diskFamilyBoundaryHomeomorph J E a).val = boundaryFamilyInclusion J E a := rfl

variable {J E}
variable {P K : Type u} [TopologicalSpace P] [TopologicalSpace K]

/-- The actual homotopy equivalence after attaching an arbitrary family
of disks along a homotopy equivalence of the old spaces. -/
def diskAttachmentBaseChangeHomotopyEquiv (r : C(BoundaryFamily J E, P))
    (e : ContinuousMap.HomotopyEquiv P K) :
    ContinuousMap.HomotopyEquiv (DiskAttachment r) (DiskAttachment (e.toFun ∘ r)) := by
  let S := diskFamilyBoundarySet J E
  let b := diskFamilyBoundaryHomeomorph J E
  have hb : ∀ a, (b a).val = boundaryFamilyInclusion J E a := fun _ => rfl
  have hi := (boundaryFamilyInclusion_isClosedEmbedding J E).injective
  let R₀ := attachmentBoundaryReparam r (boundaryFamilyInclusion J E) hi S b hb
  let R₁ := attachmentBoundaryReparam (e.toFun ∘ r) (boundaryFamilyInclusion J E) hi S b hb
  let a : C(S, P) := r.comp b.symm.toContinuousMap
  let H := attachmentBaseChangeHomotopyEquiv S (diskFamilyBoundarySet_isClosed J E)
    (diskFamilySubspace_hasHomotopyExtension E J)
    (diskFamilyFullCylinder_hasHomotopyExtension E J) a e
  exact (R₀.toHomotopyEquiv.trans H).trans R₁.symm.toHomotopyEquiv

@[simp] theorem diskAttachmentBaseChangeHomotopyEquiv_old
    (r : C(BoundaryFamily J E, P)) (e : ContinuousMap.HomotopyEquiv P K) (p : P) :
    diskAttachmentBaseChangeHomotopyEquiv r e (old r (boundaryFamilyInclusion J E) p) =
      old (e.toFun ∘ r) (boundaryFamilyInclusion J E) (e p) := rfl

@[simp] theorem diskAttachmentBaseChangeHomotopyEquiv_cell
    (r : C(BoundaryFamily J E, P)) (e : ContinuousMap.HomotopyEquiv P K)
    (d : DiskFamily J E) :
    diskAttachmentBaseChangeHomotopyEquiv r e (cell r (boundaryFamilyInclusion J E) d) =
      cell (e.toFun ∘ r) (boundaryFamilyInclusion J E) d := by
  simp only [diskAttachmentBaseChangeHomotopyEquiv, ContinuousMap.HomotopyEquiv.trans,
    ContinuousMap.comp_apply, ContinuousMap.coe_coe,
    Homeomorph.toHomotopyEquiv, attachmentBoundaryReparam_cell,
    attachmentBaseChangeHomotopyEquiv_toFun]
  let R := attachmentBoundaryReparam (e.toFun ∘ r) (boundaryFamilyInclusion J E)
    (boundaryFamilyInclusion_isClosedEmbedding J E).injective
    (diskFamilyBoundarySet J E) (diskFamilyBoundaryHomeomorph J E) (fun _ => rfl)
  exact (congrArg R.symm
    (attachmentBaseMap_cell (r.comp (diskFamilyBoundaryHomeomorph J E).symm.toContinuousMap)
      Subtype.val Subtype.val_injective e.toFun d)).trans
    (attachmentBoundaryReparam_symm_cell (e.toFun ∘ r) (boundaryFamilyInclusion J E)
      (boundaryFamilyInclusion_isClosedEmbedding J E).injective
      (diskFamilyBoundarySet J E) (diskFamilyBoundaryHomeomorph J E) (fun _ => rfl) d)

theorem diskAttachmentBaseChangeHomotopyEquiv_toFun
    (r : C(BoundaryFamily J E, P)) (e : ContinuousMap.HomotopyEquiv P K) :
    (diskAttachmentBaseChangeHomotopyEquiv r e).toFun =
      attachmentBaseMap r (boundaryFamilyInclusion J E)
        (boundaryFamilyInclusion_isClosedEmbedding J E).injective e.toFun := by
  apply hom_ext r (boundaryFamilyInclusion J E)
  · intro p
    rfl
  · intro d
    rw [diskAttachmentBaseChangeHomotopyEquiv_cell, attachmentBaseMap_cell]

/-- Moving all attaching maps through specified homotopies gives an actual
equivalence which is the identity on the old space. This permits cellular
representatives to be chosen after changing the base. -/
def diskAttachingHomotopyEquiv (r₀ r₁ : C(BoundaryFamily J E, P))
    (H : r₀.Homotopy r₁) :
    ContinuousMap.HomotopyEquiv (DiskAttachment r₀) (DiskAttachment r₁) := by
  let S := diskFamilyBoundarySet J E
  let b := diskFamilyBoundaryHomeomorph J E
  have hb : ∀ a, (b a).val = boundaryFamilyInclusion J E a := fun _ => rfl
  have hi := (boundaryFamilyInclusion_isClosedEmbedding J E).injective
  let R₀ := attachmentBoundaryReparam r₀ (boundaryFamilyInclusion J E) hi S b hb
  let R₁ := attachmentBoundaryReparam r₁ (boundaryFamilyInclusion J E) hi S b hb
  let E' := attachingHomotopyEquiv S (diskFamilyBoundarySet_isClosed J E)
    (diskFamilySubspace_hasHomotopyExtension E J)
    (diskFamilyFullCylinder_hasHomotopyExtension E J)
    (r₀.comp b.symm.toContinuousMap) (r₁.comp b.symm.toContinuousMap)
    (H.compContinuousMap b.symm.toContinuousMap)
  exact (R₀.toHomotopyEquiv.trans E').trans R₁.symm.toHomotopyEquiv

@[simp] theorem diskAttachingHomotopyEquiv_old (r₀ r₁ : C(BoundaryFamily J E, P))
    (H : r₀.Homotopy r₁) (p : P) :
    diskAttachingHomotopyEquiv r₀ r₁ H (old r₀ (boundaryFamilyInclusion J E) p) =
      old r₁ (boundaryFamilyInclusion J E) p := rfl

end FiniteChains.RelativeAttachment

namespace Whitehead
open FiniteChains.RelativeAttachment

/-- The challenge's actual zero-on-π₂ condition is retained when a disk
extension is transferred along a homotopy equivalence of its old space. -/
theorem killsPi2_diskAttachment_baseChange_iff
    {J E P K : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace P] [TopologicalSpace K]
    (r : C(BoundaryFamily J E, P)) (e : ContinuousMap.HomotopyEquiv P K) :
    KillsPi2 (⟨old (e.toFun ∘ r) (boundaryFamilyInclusion J E), old_continuous _ _⟩ :
      C(K, DiskAttachment (e.toFun ∘ r))) ↔
    KillsPi2 (⟨old r (boundaryFamilyInclusion J E), old_continuous _ _⟩ :
      C(P, DiskAttachment r)) := by
  apply killsPi2_homotopyEquiv_square_iff e (diskAttachmentBaseChangeHomotopyEquiv r e)
  have hs :
      (⟨old (e.toFun ∘ r) (boundaryFamilyInclusion J E), old_continuous _ _⟩ :
        C(K, DiskAttachment (e.toFun ∘ r))).comp e.toFun =
      (diskAttachmentBaseChangeHomotopyEquiv r e).toFun.comp
        ⟨old r (boundaryFamilyInclusion J E), old_continuous _ _⟩ := by
    apply ContinuousMap.ext
    exact fun p => (diskAttachmentBaseChangeHomotopyEquiv_old r e p).symm
  rw [hs]

theorem killsPi2_diskAttachment_homotopy_iff
    {J E P : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace P]
    (r₀ r₁ : C(BoundaryFamily J E, P)) (H : r₀.Homotopy r₁) :
    KillsPi2 (⟨old r₁ (boundaryFamilyInclusion J E), old_continuous _ _⟩ :
      C(P, DiskAttachment r₁)) ↔
    KillsPi2 (⟨old r₀ (boundaryFamilyInclusion J E), old_continuous _ _⟩ :
      C(P, DiskAttachment r₀)) := by
  apply killsPi2_homotopyEquiv_square_iff (ContinuousMap.HomotopyEquiv.refl P)
    (diskAttachingHomotopyEquiv r₀ r₁ H)
  have hs :
      (⟨old r₁ (boundaryFamilyInclusion J E), old_continuous _ _⟩ : C(P, DiskAttachment r₁)) =
      (diskAttachingHomotopyEquiv r₀ r₁ H).toFun.comp
        ⟨old r₀ (boundaryFamilyInclusion J E), old_continuous _ _⟩ := by
    apply ContinuousMap.ext
    exact fun p => (diskAttachingHomotopyEquiv_old r₀ r₁ H p).symm
  change ContinuousMap.Homotopic
    (⟨old r₁ (boundaryFamilyInclusion J E), old_continuous _ _⟩ : C(P, DiskAttachment r₁)) _
  rw [hs]

end Whitehead
