module

public import RequestProject.ConeAdjDiskAttachment
public import RequestProject.RelatorCircleFinite
public import RequestProject.PresCylinderRealizationEquiv
public import RequestProject.DiskFamilyHomotopyBaseChange

@[expose] public section

/-! The presentation-poset realization is equivalent to actual disks
attached to its subdivided rose. The attaching map of each disk is
exactly the realized letter-reading map with the specified circle
parametrization. No presentation-to-CW comparison is assumed. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb RelativeAttachment
open scoped Topology

variable {A J : Type} (w : J → List (A × Bool)) (hw : ∀ j, w j ≠ [])

local instance relatorCircleFintype (j : J) : Fintype (RelatorCircle w j) := Fintype.ofFinite _
def relatorCircleNonempty (j : J) : Nonempty (RelatorCircle w j) :=
  relatorCircle_nonempty w j (hw j)

def presOldCylinderHomeomorph :
    orderNerveRealization (ConeAdjBase (circSet w)) ≃ₜ orderNerveRealization (CylBase w) :=
  orderNerveRealizationOrderIso (coneAdjBaseOrderIso (S := circSet w))

def presOldRoseHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (orderNerveRealization (ConeAdjBase (circSet w)))
      (orderNerveRealization (Rose A)) :=
  (presOldCylinderHomeomorph w).toHomotopyEquiv.trans (presCylinderRealizationHomotopyEquiv w)

def presCircleWordMap (j : J) :
    C(orderNerveRealization (RelatorCircle w j), orderNerveRealization (Rose A)) :=
  ⟨orderNerveRealizationMap (fun c : RelatorCircle w j => aFun w c.val)
      (fun _ _ h => aFun_monotone w h),
    (orderNerveRealizationMap (fun c : RelatorCircle w j => aFun w c.val)
      (fun _ _ h => aFun_monotone w h)).hom.continuous⟩

theorem presOldRoseHomotopyEquiv_link (j : J)
    (x : orderNerveRealization (RelatorCircle w j)) :
    presOldRoseHomotopyEquiv w
      (coneAdjRealizationAttaching (circSet w)
        ⟨j, coneAdjLinkRealizationHomeomorph (circSet w)
          (RelatorCircle w) (relatorCircleOrderIso w) j x⟩) =
      presCircleWordMap w j x := by
  have hp (c : RelatorCircle w j) :
      coneAdjBaseOrderIso (coneAdjBoundaryToBase (circSet w) j
        (coneAdjLinkOrderIso (circSet w) (RelatorCircle w) (relatorCircleOrderIso w) j c)) =
      cylOuter (aHom w) c.val := by
    apply ConeAdj.inc_injective (S := circSet w)
    exact Classical.choose_spec
      (coneAdjBoundaryToBase (circSet w) j
        (coneAdjLinkOrderIso (circSet w) (RelatorCircle w)
          (relatorCircleOrderIso w) j c)).property
  change orderNerveRealizationMap (cylRetr (aHom w)) (cylRetr_monotone (aHom w))
      (orderNerveRealizationMap (coneAdjBaseOrderIso (S := circSet w))
        (coneAdjBaseOrderIso (S := circSet w)).monotone
        (orderNerveRealizationMap (coneAdjBoundaryToBase (circSet w) j)
          (coneAdjBoundaryToBase_monotone (circSet w) j)
          (orderNerveRealizationMap
            (coneAdjLinkOrderIso (circSet w) (RelatorCircle w) (relatorCircleOrderIso w) j)
            (coneAdjLinkOrderIso (circSet w) (RelatorCircle w)
              (relatorCircleOrderIso w) j).monotone x))) = _
  rw (config := { transparency := .default }) [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp,
    orderNerveRealizationMap_comp]
  have hf : (cylRetr (aHom w) ∘ coneAdjBaseOrderIso ∘ coneAdjBoundaryToBase (circSet w) j ∘
      coneAdjLinkOrderIso (circSet w) (RelatorCircle w) (relatorCircleOrderIso w) j) =
        (fun c : RelatorCircle w j => aFun w c.val) := by
    funext c
    simp only [Function.comp_apply, hp]
    rfl
  exact orderNerveRealizationMap_congr _ _ hf x

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  (b : ∀ j, orderNerveRealization (RelatorCircle w j) ≃ₜ UnitBoundary E)

def presCylinderDiskAttaching :
    C(BoundaryFamily J E, orderNerveRealization (ConeAdjBase (circSet w))) :=
  coneAdjDiskAttaching (circSet w) (RelatorCircle w) (relatorCircleOrderIso w) b

def presRoseDiskAttaching : C(BoundaryFamily J E, orderNerveRealization (Rose A)) :=
  (presOldRoseHomotopyEquiv w).toFun.comp (presCylinderDiskAttaching w b)

omit [NormedSpace ℝ E] [ProperSpace E] in
theorem presRoseDiskAttaching_link (j : J) (x : orderNerveRealization (RelatorCircle w j)) :
    presRoseDiskAttaching w b ⟨j, b j x⟩ = presCircleWordMap w j x := by
  change presOldRoseHomotopyEquiv w
    (coneAdjDiskAttaching (circSet w) (RelatorCircle w) (relatorCircleOrderIso w) b ⟨j, b j x⟩) = _
  rw (config := { transparency := .default }) [coneAdjDiskAttaching_link]
  exact presOldRoseHomotopyEquiv_link w j x

omit [NormedSpace ℝ E] [ProperSpace E] in
theorem presRoseDiskAttaching_apply (z : BoundaryFamily J E) :
    presRoseDiskAttaching w b z = presCircleWordMap w z.1 ((b z.1).symm z.2) := by
  rcases z with ⟨j, y⟩
  simpa only [Homeomorph.apply_symm_apply] using
    presRoseDiskAttaching_link w b j ((b j).symm y)

/-- Both the cone attachment and the mapping-cylinder collapse are actual
maps; this equivalence has no unproved CW-model comparison as an input. -/
def presRealizationRoseDiskHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (orderNerveRealization (PresPos w))
      (DiskAttachment (presRoseDiskAttaching w b)) := by
  letI : ∀ j, Nonempty (RelatorCircle w j) := fun j => relatorCircle_nonempty w j (hw j)
  exact (coneAdjRealizationDiskHomeomorph (circSet w) (RelatorCircle w)
    (relatorCircleOrderIso w) b).toHomotopyEquiv.trans
      (diskAttachmentBaseChangeHomotopyEquiv (presCylinderDiskAttaching w b)
        (presOldRoseHomotopyEquiv w))

@[simp] theorem presRealizationRoseDiskHomotopyEquiv_old
    (x : orderNerveRealization (ConeAdjBase (circSet w))) :
    presRealizationRoseDiskHomotopyEquiv w hw b (coneAdjRealizationOld (circSet w) x) =
      old (presRoseDiskAttaching w b) (boundaryFamilyInclusion J E)
        (presOldRoseHomotopyEquiv w x) := by
  letI : ∀ j, Nonempty (RelatorCircle w j) := fun j => relatorCircle_nonempty w j (hw j)
  change diskAttachmentBaseChangeHomotopyEquiv _ _
    (coneAdjRealizationDiskHomeomorph _ _ _ _ (coneAdjRealizationOld _ x)) = _
  rw (config := { transparency := .default }) [coneAdjRealizationDiskHomeomorph_old, diskAttachmentBaseChangeHomotopyEquiv_old]
  rfl

end FiniteChains.PresModel

