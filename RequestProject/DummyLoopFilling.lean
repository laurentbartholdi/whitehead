import RequestProject.HomeomorphContinuousMap
import RequestProject.PointAttachmentFilling
import RequestProject.PointAttachmentBaseChange
import RequestProject.OrderRoseRealizationHomeomorph

/-! Adding one dummy loop and its filling disk is a genuine homotopy
equivalence on an arbitrary old space. The equivalence's forward map is
exactly the composite of the two old-space inclusions. -/

noncomputable section
namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
open scoped Topology

/-- An actual parametrized circle, including the direction of its
once-around traversal. It is not a chosen homotopy-type comparison. -/
def dummyCircleBoundaryHomeomorph : UnitBoundary (Fin 2 → ℝ) ≃ₜ Rose PUnit :=
  PresModel.roseFourCycle.boundaryHomeomorph.symm.trans
    (PresModel.orderRoseRealizationHomeomorph PUnit)

variable {X : Type} [TopologicalSpace X] (x : X)

def dummyOneAttaching : C(BoundaryFamily PUnit (Fin 1 → ℝ), X) :=
  ContinuousMap.const _ x

def dummyLoopMap : C(Rose PUnit, DiskAttachment (dummyOneAttaching x)) :=
  singletonAttachmentInto x (boundaryFamilyInclusion PUnit (Fin 1 → ℝ))
    (boundaryFamilyInclusion_isClosedEmbedding PUnit (Fin 1 → ℝ)).injective

def dummyFillingBoundary : C(UnitBoundary (Fin 2 → ℝ), DiskAttachment (dummyOneAttaching x)) :=
  (dummyLoopMap x).comp dummyCircleBoundaryHomeomorph.toContinuousMap

def dummyTwoAttaching :
    C(BoundaryFamily PUnit (Fin 2 → ℝ), DiskAttachment (dummyOneAttaching x)) :=
  singletonDiskAttaching (dummyFillingBoundary x)

abbrev DummyLoopFilled := DiskAttachment (dummyTwoAttaching x)

def dummyLoopPointHomeomorph :
    PointAttachment x (roseVertex PUnit) ≃ₜ DiskAttachment (dummyOneAttaching x) :=
  pointAttachmentBaseChangeHomeomorph x (boundaryFamilyInclusion PUnit (Fin 1 → ℝ))
    (boundaryFamilyInclusion_isClosedEmbedding PUnit (Fin 1 → ℝ)).injective

@[simp] theorem dummyLoopPointHomeomorph_old (y : X) :
    dummyLoopPointHomeomorph x (pointOld x (roseVertex PUnit) y) =
      old (dummyOneAttaching x) (boundaryFamilyInclusion PUnit (Fin 1 → ℝ)) y :=
  pointAttachmentBaseChangeHomeomorph_old ..

@[simp] theorem dummyLoopPointHomeomorph_cell (y : Rose PUnit) :
    dummyLoopPointHomeomorph x (pointCell x (roseVertex PUnit) y) = dummyLoopMap x y :=
  pointAttachmentBaseChangeHomeomorph_cell ..

def dummyPointFillingHomeomorph :
    FilledPointAttachment x (roseVertex PUnit) dummyCircleBoundaryHomeomorph
        (unitBoundaryInclusion (Fin 2 → ℝ)) ≃ₜ
      Space (dummyFillingBoundary x) (unitBoundaryInclusion (Fin 2 → ℝ)) :=
  attachmentDiagramHomeomorph
    (pointFillAttaching x (roseVertex PUnit) dummyCircleBoundaryHomeomorph)
    (unitBoundaryInclusion (Fin 2 → ℝ))
    (dummyFillingBoundary x) (unitBoundaryInclusion (Fin 2 → ℝ))
    (Equiv.refl _) (dummyLoopPointHomeomorph x) (Homeomorph.refl _)
    (fun a => dummyLoopPointHomeomorph_cell x (dummyCircleBoundaryHomeomorph a))
    (fun _ => rfl)
    (fun _ _ h => Subtype.ext (congrArg (fun z : ClosedUnitBall (Fin 2 → ℝ) => z.val) h))
    (fun _ _ h => Subtype.ext (congrArg (fun z : ClosedUnitBall (Fin 2 → ℝ) => z.val) h))

def dummyLoopFillingHomotopyEquiv : ContinuousMap.HomotopyEquiv X (DummyLoopFilled x) :=
  ((pointBoundaryFillingHomotopyEquiv x (roseVertex PUnit) dummyCircleBoundaryHomeomorph).trans
    (dummyPointFillingHomeomorph x).toHomotopyEquiv).trans
      (singletonDiskAttachmentHomeomorph (dummyFillingBoundary x)).symm.toHomotopyEquiv

def dummyLoopFillingOld : C(X, DummyLoopFilled x) :=
  (⟨old (dummyTwoAttaching x) (boundaryFamilyInclusion PUnit (Fin 2 → ℝ)),
    old_continuous _ _⟩ : C(DiskAttachment (dummyOneAttaching x), _)).comp
      ⟨old (dummyOneAttaching x) (boundaryFamilyInclusion PUnit (Fin 1 → ℝ)), old_continuous _ _⟩

theorem dummyLoopFillingHomotopyEquiv_apply (y : X) :
    dummyLoopFillingHomotopyEquiv x y = dummyLoopFillingOld x y := by
  change (singletonDiskAttachmentHomeomorph (dummyFillingBoundary x)).symm
    (dummyPointFillingHomeomorph x
      (pointBoundaryFillingHomotopyEquiv x (roseVertex PUnit) dummyCircleBoundaryHomeomorph y)) = _
  rw [pointBoundaryFillingHomotopyEquiv_old]
  change (singletonDiskAttachmentHomeomorph (dummyFillingBoundary x)).symm
    (dummyPointFillingHomeomorph x
      (old (pointFillAttaching x (roseVertex PUnit) dummyCircleBoundaryHomeomorph)
        (unitBoundaryInclusion (Fin 2 → ℝ)) (pointOld x (roseVertex PUnit) y))) = _
  rw [show dummyPointFillingHomeomorph x
      (old (pointFillAttaching x (roseVertex PUnit) dummyCircleBoundaryHomeomorph)
        (unitBoundaryInclusion (Fin 2 → ℝ)) (pointOld x (roseVertex PUnit) y)) =
      old (dummyFillingBoundary x) (unitBoundaryInclusion (Fin 2 → ℝ))
        (dummyLoopPointHomeomorph x (pointOld x (roseVertex PUnit) y)) from
          attachmentDiagramHomeomorph_old ..]
  rw [dummyLoopPointHomeomorph_old]
  apply (singletonDiskAttachmentHomeomorph (dummyFillingBoundary x)).injective
  rw [Homeomorph.apply_symm_apply]
  exact (singletonDiskAttachmentHomeomorph_old (dummyFillingBoundary x)
    (old (dummyOneAttaching x) (boundaryFamilyInclusion PUnit (Fin 1 → ℝ)) y)).symm

theorem dummyLoopFillingHomotopyEquiv_toFun :
    (dummyLoopFillingHomotopyEquiv x).toFun = dummyLoopFillingOld x :=
  ContinuousMap.ext (dummyLoopFillingHomotopyEquiv_apply x)

end FiniteChains.ClassicalGraphModel
