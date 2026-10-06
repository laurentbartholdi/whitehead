module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.ConeAdjRealizationAttachment
public import RequestProject.OrderNerveLowerCone
public import RequestProject.AttachmentDiagramHomeomorph
public import RequestProject.ClassicalCellAttachmentMaps

@[expose] public section

/-! Replace the actual cone pieces by disks and their actual strict
boundaries by spheres, preserving the old inclusion. Circle geometry is
provided separately, one finite link at a time; the collection of cones
need not be finite. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open scoped Topology
open RelativeAttachment

variable {P J : Type} [PartialOrder P] (S : J → P → Prop)
  (C : J → Type) [∀ j, PartialOrder (C j)] [∀ j, Fintype (C j)] [∀ j, Nonempty (C j)]
  (e : ∀ j, C j ≃o StrictBelow (ConeAdj.apex (S := S) j))
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  (b : ∀ j, orderNerveRealization (C j) ≃ₜ UnitBoundary E)

def coneAdjLinkOrderIso (j : J) : C j ≃o ConeAdjBoundary S j :=
  (e j).trans (coneAdjBoundaryOrderIso S j).symm

def coneAdjLinkRealizationHomeomorph (j : J) :
    orderNerveRealization (C j) ≃ₜ orderNerveRealization (ConeAdjBoundary S j) :=
  orderNerveRealizationOrderIso (coneAdjLinkOrderIso S C e j)

def coneAdjSphereHomeomorph (j : J) :
    orderNerveRealization (ConeAdjBoundary S j) ≃ₜ UnitBoundary E :=
  (coneAdjLinkRealizationHomeomorph S C e j).symm.trans (b j)

def coneAdjBallHomeomorph (j : J) :
    orderNerveRealization (ConeAdjDisk S j) ≃ₜ ClosedUnitBall E :=
  lowerConeBallHomeomorph (ConeAdj.apex j) (e j) (b j)

omit [∀ j, Fintype (C j)] [∀ j, Nonempty (C j)] in
theorem coneAdjLinkRealization_boundary (j : J) (x : orderNerveRealization (C j)) :
    orderNerveRealizationMap (Subtype.val : ConeAdjBoundary S j → ConeAdjDisk S j)
        (fun _ _ h => h) (coneAdjLinkRealizationHomeomorph S C e j x) =
      orderNerveRealizationMap (lowerConeBoundary (ConeAdj.apex j) (e j))
        (lowerConeBoundary (ConeAdj.apex j) (e j)).monotone x := by
  change orderNerveRealizationMap Subtype.val (fun _ _ h => h)
      (orderNerveRealizationMap (coneAdjLinkOrderIso S C e j)
        (coneAdjLinkOrderIso S C e j).monotone x) = _
  rw (config := { transparency := .default }) [orderNerveRealizationMap_comp]
  rfl

theorem coneAdjBallHomeomorph_boundary (j : J)
    (x : orderNerveRealization (ConeAdjBoundary S j)) :
    coneAdjBallHomeomorph S C e b j
        (orderNerveRealizationMap Subtype.val (fun _ _ h => h) x) =
      unitBoundaryInclusion E (coneAdjSphereHomeomorph S C e b j x) := by
  have h := lowerConeBallHomeomorph_boundary (ConeAdj.apex (S := S) j) (e j) (b j)
    ((coneAdjLinkRealizationHomeomorph S C e j).symm x)
  rw (config := { transparency := .default }) [← coneAdjLinkRealization_boundary S C e j, Homeomorph.apply_symm_apply] at h
  exact h

def coneAdjSphereFamilyHomeomorph :
    (Σ j, orderNerveRealization (ConeAdjBoundary S j)) ≃ₜ BoundaryFamily J E :=
  sigmaFiberHomeomorph (coneAdjSphereHomeomorph S C e b)

def coneAdjBallFamilyHomeomorph :
    (Σ j, orderNerveRealization (ConeAdjDisk S j)) ≃ₜ DiskFamily J E :=
  sigmaFiberHomeomorph (coneAdjBallHomeomorph S C e b)

def coneAdjDiskAttaching : C(BoundaryFamily J E, orderNerveRealization (ConeAdjBase S)) :=
  (coneAdjRealizationAttaching S).comp (coneAdjSphereFamilyHomeomorph S C e b).symm.toContinuousMap

omit [∀ j, Fintype (C j)] [∀ j, Nonempty (C j)] [NormedSpace ℝ E] [ProperSpace E] in
theorem coneAdjDiskAttaching_link (j : J) (x : orderNerveRealization (C j)) :
    coneAdjDiskAttaching S C e b ⟨j, b j x⟩ =
      coneAdjRealizationAttaching S ⟨j, coneAdjLinkRealizationHomeomorph S C e j x⟩ := by
  have hs : coneAdjSphereFamilyHomeomorph S C e b
      ⟨j, coneAdjLinkRealizationHomeomorph S C e j x⟩ = ⟨j, b j x⟩ := by
    change (⟨j, b j ((coneAdjLinkRealizationHomeomorph S C e j).symm
      (coneAdjLinkRealizationHomeomorph S C e j x))⟩ : BoundaryFamily J E) = _
    rw (config := { transparency := .default }) [Homeomorph.symm_apply_apply]
  change coneAdjRealizationAttaching S
    ((coneAdjSphereFamilyHomeomorph S C e b).symm ⟨j, b j x⟩) = _
  rw (config := { transparency := .default }) [← hs, Homeomorph.symm_apply_apply]

theorem coneAdjRealizationBoundary_injective : Function.Injective (coneAdjRealizationBoundary S) := by
  rintro ⟨j, x⟩ ⟨k, y⟩ h
  have hk : j = k := congrArg Sigma.fst h
  subst k
  exact congrArg (Sigma.mk j) (orderNerveRealizationMap_injective
    (Subtype.val : ConeAdjBoundary S j → ConeAdjDisk S j) (fun _ _ h => h)
    Subtype.val_injective (eq_of_heq (Sigma.mk.inj h).2))

def coneAdjAttachmentDiskHomeomorph :
    RelativeAttachment.Space (coneAdjRealizationAttaching S) (coneAdjRealizationBoundary S)
      ≃ₜ DiskAttachment (coneAdjDiskAttaching S C e b) :=
  attachmentDiagramHomeomorph
    (coneAdjRealizationAttaching S) (coneAdjRealizationBoundary S)
    (coneAdjDiskAttaching S C e b) (boundaryFamilyInclusion J E)
    (coneAdjSphereFamilyHomeomorph S C e b).toEquiv (Homeomorph.refl _)
    (coneAdjBallFamilyHomeomorph S C e b)
    (fun a => by
      change coneAdjRealizationAttaching S a = coneAdjRealizationAttaching S
        ((coneAdjSphereFamilyHomeomorph S C e b).symm
          (coneAdjSphereFamilyHomeomorph S C e b a))
      rw (config := { transparency := .default }) [Homeomorph.symm_apply_apply])
    (fun a => by
      rcases a with ⟨j, x⟩
      exact congrArg (Sigma.mk j) (coneAdjBallHomeomorph_boundary S C e b j x))
    (boundaryFamilyInclusion_isClosedEmbedding J E).injective
    (coneAdjRealizationBoundary_injective S)

/-- The realization is a genuine family of disks attached to its old part. -/
def coneAdjRealizationDiskHomeomorph :
    orderNerveRealization (ConeAdj S) ≃ₜ DiskAttachment (coneAdjDiskAttaching S C e b) :=
  (coneAdjRealizationAttachmentHomeomorph S).symm.trans
    (coneAdjAttachmentDiskHomeomorph S C e b)

@[simp] theorem coneAdjRealizationDiskHomeomorph_old
    (x : orderNerveRealization (ConeAdjBase S)) :
    coneAdjRealizationDiskHomeomorph S C e b (coneAdjRealizationOld S x) =
      old (coneAdjDiskAttaching S C e b) (boundaryFamilyInclusion J E) x := by
  rw (config := { transparency := .default }) [← coneAdjRealizationAttachmentHomeomorph_old]
  change coneAdjAttachmentDiskHomeomorph S C e b
    ((coneAdjRealizationAttachmentHomeomorph S).symm
      (coneAdjRealizationAttachmentHomeomorph S _)) = _
  rw (config := { transparency := .default }) [Homeomorph.symm_apply_apply]
  exact attachmentDiagramHomeomorph_old ..

@[simp] theorem coneAdjRealizationDiskHomeomorph_cell
    (z : Σ j, orderNerveRealization (ConeAdjDisk S j)) :
    coneAdjRealizationDiskHomeomorph S C e b (coneAdjRealizationCell S z) =
      cell (coneAdjDiskAttaching S C e b) (boundaryFamilyInclusion J E)
        (coneAdjBallFamilyHomeomorph S C e b z) := by
  rw (config := { transparency := .default }) [← coneAdjRealizationAttachmentHomeomorph_cell]
  change coneAdjAttachmentDiskHomeomorph S C e b
    ((coneAdjRealizationAttachmentHomeomorph S).symm
      (coneAdjRealizationAttachmentHomeomorph S _)) = _
  rw (config := { transparency := .default }) [Homeomorph.symm_apply_apply]
  exact attachmentDiagramHomeomorph_cell ..

end FiniteChains.Comb
