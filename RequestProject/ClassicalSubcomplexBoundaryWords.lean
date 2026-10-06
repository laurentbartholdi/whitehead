module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.ClassicalSubcomplexGraphNaturality
public import RequestProject.BoundaryWordNaturality

@[expose] public section

/-! Every original two-cell has a boundary word in the exact graph of
its subcomplex. These data can be pushed along original inclusions,
including their actual attaching homotopy. Unverified source. -/

noncomputable section
namespace FiniteChains.ClassicalCW
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment
open Set Topology
open scoped Classical
variable {X : Type} [TopologicalSpace X] [T2Space X] [CWComplex (Set.univ : Set X)]
  {C D : CWComplex.Subcomplex (Set.univ : Set X)}

def subcomplexCellBoundary (C : CWComplex.Subcomplex (Set.univ : Set X))
    (j : RelCWComplex.cell (C : Set X) 2) :
    C(UnitBoundary (Fin 2 → ℝ), DiskAttachment (skeletonAttachingMap (C : Set X) 1)) := by
  let a : C(UnitBoundary (Fin 2 → ℝ),
      BoundaryFamily (RelCWComplex.cell (C : Set X) 2) (Fin 2 → ℝ)) :=
    ⟨fun x => ⟨j, x⟩, continuous_sigmaMk
      (σ := fun _ : RelCWComplex.cell (C : Set X) 2 => UnitBoundary (Fin 2 → ℝ)) (i := j)⟩
  exact (skeletonAsDiskAttachment (C : Set X) 1).toContinuousMap.comp
    ((skeletonAttachingMap (C : Set X) 2).comp a)

theorem subcomplexCellBoundary_natural (h : (C : Set X) ⊆ D)
    (j : RelCWComplex.cell (C : Set X) 2) :
    (subcomplexGraphDiskMap h).comp (subcomplexCellBoundary C j) =
      subcomplexCellBoundary D (subcomplexCellInclusion h 2 j) := by
  ext a
  apply (skeletonAttachmentHomeomorph (D : Set X) 1).injective
  change skeletonAttachmentHomeomorph (D : Set X) 1
    (subcomplexGraphDiskMap h (subcomplexCellBoundary C j a)) =
    skeletonAttachmentHomeomorph (D : Set X) 1
      (subcomplexCellBoundary D (subcomplexCellInclusion h 2 j) a)
  rw [subcomplexGraphDiskMap_skeleton]
  change subcomplexSkeletonInclusion h 2
      ((skeletonAttachmentHomeomorph (C : Set X) 1)
        ((skeletonAttachmentHomeomorph (C : Set X) 1).symm _)) =
    (skeletonAttachmentHomeomorph (D : Set X) 1)
      ((skeletonAttachmentHomeomorph (D : Set X) 1).symm _)
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  apply Subtype.ext
  rfl

theorem subcomplexCellBoundary_word_exists
    (C : CWComplex.Subcomplex (Set.univ : Set X))
    (j : RelCWComplex.cell (C : Set X) 2) :
    ∃ W : BoundaryWords (skeletonAttachingMap (C : Set X) 1),
      (subcomplexCellBoundary C j).Homotopic W.boundaryMap := by
  letI := subcomplexZeroSkeleton_discrete C
  exact boundaryMap_homotopic_boundaryWords (skeletonAttachingMap (C : Set X) 1)
    (skeletonAttachingMap (C : Set X) 1).continuous (subcomplexCellBoundary C j)

theorem subcomplexBoundaryWord_map (h : (C : Set X) ⊆ D)
    (W : BoundaryWords (skeletonAttachingMap (C : Set X) 1)) :
    (subcomplexGraphDiskMap h).comp W.boundaryMap =
      (W.map (subcomplexGraphInclusion h)).boundaryMap :=
  W.boundaryMap_map (subcomplexGraphInclusion h) (subcomplexGraphDiskMap h)
    (subcomplexGraphDiskMap_old h) (subcomplexGraphDiskMap_edge h)

theorem subcomplexCellBoundary_word_transport (h : (C : Set X) ⊆ D)
    (j : RelCWComplex.cell (C : Set X) 2)
    (W : BoundaryWords (skeletonAttachingMap (C : Set X) 1))
    (hW : (subcomplexCellBoundary C j).Homotopic W.boundaryMap) :
    (subcomplexCellBoundary D (subcomplexCellInclusion h 2 j)).Homotopic
      (W.map (subcomplexGraphInclusion h)).boundaryMap := by
  have H := (ContinuousMap.Homotopic.refl (subcomplexGraphDiskMap h)).comp hW
  rwa [subcomplexCellBoundary_natural, subcomplexBoundaryWord_map] at H

end FiniteChains.ClassicalCW
