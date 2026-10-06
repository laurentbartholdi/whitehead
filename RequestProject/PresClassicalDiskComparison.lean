import RequestProject.HomeomorphContinuousMap
import RequestProject.PresRealizationWordDiskComparison
import RequestProject.OrderRoseRealizationHomeomorph

/-! A presentation realization and a literal bouquet of interval circles
with genuine two-disks have a constructed homotopy equivalence. All cone,
circle and bouquet identifications are instantiated by explicit maps. -/

noncomputable section
namespace FiniteChains.PresModel
open Comb RelativeAttachment
open scoped Topology

variable {A J : Type} (w : J → List (A × Bool)) (hw : ∀ j, w j ≠ [])

def classicalPresWordAttaching :
    C(BoundaryFamily J (Fin 2 → ℝ), ClassicalGraphModel.Rose A) :=
  (orderRoseRealizationHomeomorph A).toContinuousMap.comp (actualPresWordAttaching w hw)

abbrev ClassicalPresWordDisks := DiskAttachment (classicalPresWordAttaching w hw)

def presClassicalDiskComparison :
    ContinuousMap.HomotopyEquiv (orderNerveRealization (PresPos w)) (ClassicalPresWordDisks w hw) :=
  (actualPresWordDiskComparison w hw).trans
    (diskAttachmentBaseChangeHomotopyEquiv (actualPresWordAttaching w hw)
      (orderRoseRealizationHomeomorph A).toHomotopyEquiv)

theorem classicalPresWordAttaching_apply (z : BoundaryFamily J (Fin 2 → ℝ)) :
    classicalPresWordAttaching w hw z =
      orderRoseRealizationHomeomorph A
        (presCircleWordMap w z.1 ((presCircleBoundaryHomeomorph w hw z.1).symm z.2)) := by
  change orderRoseRealizationHomeomorph A (actualPresWordAttaching w hw z) = _
  rw [actualPresWordAttaching_apply]

theorem classicalPresWordAttaching_link (j : J) (x : orderNerveRealization (RelatorCircle w j)) :
    classicalPresWordAttaching w hw ⟨j, presCircleBoundaryHomeomorph w hw j x⟩ =
      orderRoseRealizationHomeomorph A (presCircleWordMap w j x) := by
  change orderRoseRealizationHomeomorph A
    (actualPresWordAttaching w hw ⟨j, presCircleBoundaryHomeomorph w hw j x⟩) = _
  rw [actualPresWordAttaching_link]

@[simp] theorem presClassicalDiskComparison_old
    (x : orderNerveRealization (ConeAdjBase (circSet w))) :
    presClassicalDiskComparison w hw (coneAdjRealizationOld (circSet w) x) =
      old (classicalPresWordAttaching w hw) (boundaryFamilyInclusion J (Fin 2 → ℝ))
        (orderRoseRealizationHomeomorph A (presOldRoseHomotopyEquiv w x)) := by
  change diskAttachmentBaseChangeHomotopyEquiv _ _
    (actualPresWordDiskComparison w hw (coneAdjRealizationOld (circSet w) x)) = _
  rw [actualPresWordDiskComparison_old, diskAttachmentBaseChangeHomotopyEquiv_old]
  rfl

end FiniteChains.PresModel
