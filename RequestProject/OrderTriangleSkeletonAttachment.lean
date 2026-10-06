module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.OrderTriangleDiskCoordinates
public import RequestProject.StrictOrderNerveCellEquivalences
public import RequestProject.DiskAttachmentQuotientReparametrization
public import RequestProject.ClassicalCWSkeletonAttachment
public import RequestProject.OrderNerveRealizationCW
public import RequestProject.OrderNerveTwoComplex
public import RequestProject.ClassicalCWWordDiskModel

@[expose] public section

/-! The actual second skeleton of an order realization is obtained by
attaching explicitly parametrized triangle disks to its actual first
skeleton. The proof replaces the original chosen characteristic charts
through disk quotient maps, so no orientation assumption is needed.
Awaiting final Lean verification. -/

noncomputable section
open scoped Classical Topology
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.OrderTriangleAttachment
open RelativeAttachment ClassicalSkeletonAttachment CategoryTheory Topology

def metricBallNormBallHomeomorph (n : ℕ) :
    (Metric.closedBall 0 1 : Set (Fin n → ℝ)) ≃ₜ ClosedUnitBall (Fin n → ℝ) where
  toFun x := ⟨x.val, by simpa only [Metric.mem_closedBall, dist_zero_right] using x.property⟩
  invFun x := ⟨x.val, by simpa only [Metric.mem_closedBall, dist_zero_right] using x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

def simplexNormDiskHomeomorph (n : ℕ) :
    stdSimplex ℝ (Fin (n + 1)) ≃ₜ ClosedUnitBall (Fin n → ℝ) :=
  (standardSimplexClosedBallHomeomorph n).trans (metricBallNormBallHomeomorph n)

theorem simplexNormDiskHomeomorph_positive_iff (n : ℕ)
    (z : stdSimplex ℝ (Fin (n + 1))) :
    (∀ i, 0 < z.val i) ↔ ‖(simplexNormDiskHomeomorph n z).val‖ < 1 := by
  change (∀ i, 0 < z.val i) ↔ ‖(standardSimplexClosedBallHomeomorph n z).val‖ < 1
  simpa only [Metric.mem_ball, dist_zero_right] using
    standardSimplexClosedBallHomeomorph_positive_iff n z

def diskReparametrization : C(ClosedUnitBall (Fin 2 → ℝ), ClosedUnitBall (Fin 2 → ℝ)) :=
  (simplexNormDiskHomeomorph 2).toContinuousMap.comp OrderTriangleDisk.disk

theorem diskReparametrization_interior (x : ClosedUnitBall (Fin 2 → ℝ)) :
    ‖(diskReparametrization x).val‖ < 1 ↔ ‖x.val‖ < 1 :=
  (simplexNormDiskHomeomorph_positive_iff 2 (OrderTriangleDisk.disk x)).symm.trans
    (OrderTriangleDisk.disk_positive_iff x)

theorem diskReparametrization_isQuotientMap : IsQuotientMap diskReparametrization :=
  (simplexNormDiskHomeomorph 2).isQuotientMap.comp OrderTriangleDisk.disk_isQuotientMap

theorem diskReparametrization_injective_interior :
    Set.InjOn diskReparametrization {x | ‖x.val‖ < 1} := by
  intro x hx y hy h
  exact OrderTriangleDisk.disk_injOn_interior hx hy ((simplexNormDiskHomeomorph 2).injective h)

def boundaryReparametrization : C(UnitBoundary (Fin 2 → ℝ), UnitBoundary (Fin 2 → ℝ)) where
  toFun z := ⟨(diskReparametrization (unitBoundaryInclusion _ z)).val, by
    apply le_antisymm (diskReparametrization (unitBoundaryInclusion _ z)).property
    apply le_of_not_gt
    intro h
    have h' := (diskReparametrization_interior (unitBoundaryInclusion _ z)).mp h
    change ‖z.val‖ < 1 at h'
    rw [z.property] at h'
    exact (lt_irrefl _ h')⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp diskReparametrization.continuous).comp
      (unitBoundaryInclusion (Fin 2 → ℝ)).continuous

theorem diskReparametrization_boundary (z : UnitBoundary (Fin 2 → ℝ)) :
    diskReparametrization (unitBoundaryInclusion _ z) =
      unitBoundaryInclusion _ (boundaryReparametrization z) := rfl

variable (P : Type) [PartialOrder P]

abbrev OneSkeleton := SkeletonCarrier (Set.univ : Set (orderNerveRealization P)) 2
abbrev TwoSkeleton := SkeletonCarrier (Set.univ : Set (orderNerveRealization P)) 3

def triangleDiskMap (t : StrictOrdTri P) :
    C(ClosedUnitBall (Fin 2 → ℝ), orderNerveRealization P) where
  toFun x := orderNerveRealizationSimplex P (strictTriNerveEquiv P t).val
    (ULift.up ((TopologicalSingular.simplexCoordinates 2).symm (OrderTriangleDisk.disk x)))
  continuous_toFun := (orderNerveRealizationSimplex P (strictTriNerveEquiv P t).val).hom.continuous.comp
    (continuous_uliftUp.comp
      ((TopologicalSingular.simplexCoordinates 2).symm.continuous.comp OrderTriangleDisk.disk.continuous))

theorem characteristicDisk_simplex (n : ℕ) (s : (nerve P).nonDegenerate n)
    (z : stdSimplex ℝ (Fin (n + 1))) :
    Topology.CWComplex.map (C := (Set.univ : Set (orderNerveRealization P))) n s
      (simplexNormDiskHomeomorph n z).val =
        orderNerveRealizationSimplex P s.val (ULift.up ((TopologicalSingular.simplexCoordinates n).symm z)) := by
  rw [show Topology.CWComplex.map (C := (Set.univ : Set (orderNerveRealization P))) n s
      (simplexNormDiskHomeomorph n z).val =
        orderNerveClosedBallChart s (standardSimplexClosedBallHomeomorph n z) from
    orderNerveCharacteristicFunction_closedBall s (standardSimplexClosedBallHomeomorph n z)]
  change orderNerveRealizationSimplex P s.val
    (ULift.up ((TopologicalSingular.simplexCoordinates n).symm
      ((standardSimplexClosedBallHomeomorph n).symm
      (standardSimplexClosedBallHomeomorph n z)))) = _
  rw [Homeomorph.symm_apply_apply]

theorem triangleDiskMap_characteristic (t : StrictOrdTri P)
    (x : ClosedUnitBall (Fin 2 → ℝ)) :
    Topology.CWComplex.map (C := (Set.univ : Set (orderNerveRealization P))) 2
      (strictTriNerveEquiv P t) (diskReparametrization x).val = triangleDiskMap P t x :=
  characteristicDisk_simplex P 2 (strictTriNerveEquiv P t) (OrderTriangleDisk.disk x)

def triangleAttaching : C(BoundaryFamily (StrictOrdTri P) (Fin 2 → ℝ), OneSkeleton P) where
  toFun := reparametrizedAttaching
    (skeletonAttachingMap (Set.univ : Set (orderNerveRealization P)) 2)
    (strictTriNerveEquiv P) (fun _ => boundaryReparametrization)
  continuous_toFun := by
    apply continuous_sigma
    intro t
    have hs : Continuous (Sigma.mk
        (β := fun _ : (nerve P).nonDegenerate 2 => UnitBoundary (Fin 2 → ℝ))
        (strictTriNerveEquiv P t)) := continuous_sigmaMk
    exact (skeletonAttachingMap (Set.univ : Set (orderNerveRealization P)) 2).continuous.comp
      (hs.comp boundaryReparametrization.continuous)

theorem triangleAttaching_val (t : StrictOrdTri P) (z : UnitBoundary (Fin 2 → ℝ)) :
    (triangleAttaching P ⟨t, z⟩).val = triangleDiskMap P t (unitBoundaryInclusion _ z) :=
  triangleDiskMap_characteristic P t (unitBoundaryInclusion _ z)

def triangleReparametrizationHomeomorph :
    DiskAttachment (triangleAttaching P) ≃ₜ
      DiskAttachment (skeletonAttachingMap (Set.univ : Set (orderNerveRealization P)) 2) :=
  diskAttachmentQuotientReparametrization
    (skeletonAttachingMap (Set.univ : Set (orderNerveRealization P)) 2)
    (strictTriNerveEquiv P) (fun _ => diskReparametrization)
    (fun _ => boundaryReparametrization) (fun _ => diskReparametrization_boundary)
    (fun _ => diskReparametrization_isQuotientMap)
    (fun _ => diskReparametrization_interior)
    (fun _ => diskReparametrization_injective_interior)

def triangleAttachmentHomeomorph : DiskAttachment (triangleAttaching P) ≃ₜ TwoSkeleton P :=
  (triangleReparametrizationHomeomorph P).trans
    (skeletonAttachmentHomeomorph (Set.univ : Set (orderNerveRealization P)) 2)

@[simp] theorem triangleAttachmentHomeomorph_old (x : OneSkeleton P) :
    (triangleAttachmentHomeomorph P
      (old (triangleAttaching P) (boundaryFamilyInclusion (StrictOrdTri P) _) x)).val = x.val := rfl

@[simp] theorem triangleAttachmentHomeomorph_cell (t : StrictOrdTri P)
    (x : ClosedUnitBall (Fin 2 → ℝ)) :
    (triangleAttachmentHomeomorph P
      (cell (triangleAttaching P) (boundaryFamilyInclusion (StrictOrdTri P) _) ⟨t, x⟩)).val =
        triangleDiskMap P t x := by
  change (skeletonAttachmentHomeomorph (Set.univ : Set (orderNerveRealization P)) 2
    (triangleReparametrizationHomeomorph P (cell _ _ ⟨t, x⟩))).val = _
  rw [triangleReparametrizationHomeomorph]
  erw [diskAttachmentQuotientReparametrization_cell]
  rw [skeletonAttachmentHomeomorph_cell]
  exact triangleDiskMap_characteristic P t x

/-- When the nerve is two-dimensional, these are all the cells of the
actual realization, not just an auxiliary finite or truncated space. -/
def triangleAttachmentRealizationHomeomorph [Nonempty P]
    [(nerve P).HasDimensionLE 2] (hP : IsConnected (orderCx P)) :
    DiskAttachment (triangleAttaching P) ≃ₜ orderNerveRealization P :=
  (triangleAttachmentHomeomorph P).trans
    (ClassicalCW.originalTopSkeletonHomeomorph (orderNerveTwoComplex P hP)).symm

end FiniteChains.Comb.OrderTriangleAttachment
