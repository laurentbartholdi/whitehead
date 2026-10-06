module

public import RequestProject.ClassicalCWChainDiskModels

@[expose] public section

/-! The coherent word-disk models form actual commuting squares with
the original subcomplex inclusions. Thus original topological pi2
vanishing transfers to the constructed model inclusions. Unverified. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.ClassicalCW
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment
open Set Topology
open scoped Classical
variable (K : Whitehead.TwoComplex)

theorem subcomplexAsDiskAttachment_natural
    {C D : CWComplex.Subcomplex (Set.univ : Set K)} (h : (C : Set K) ⊆ D)
    (x : (C : Set K)) :
    subcomplexAsDiskAttachment K D (Set.inclusion h x) =
      subcomplexDiskMap h 2 (subcomplexAsDiskAttachment K C x) := by
  apply (skeletonAttachmentHomeomorph (D : Set K) 2).injective
  rw [subcomplexDiskMap_skeleton]
  change (skeletonAttachmentHomeomorph (D : Set K) 2)
      ((skeletonAttachmentHomeomorph (D : Set K) 2).symm _) =
    subcomplexSkeletonInclusion h 3
      ((skeletonAttachmentHomeomorph (C : Set K) 2)
        ((skeletonAttachmentHomeomorph (C : Set K) 2).symm _))
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  rfl

namespace ChainWords
variable {n : ℕ} (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C)
  [Choices C]

omit [Choices C] in
theorem rawAttaching_natural {i k : Fin (n + 1)} (hik : i ≤ k)
    (j : RelCWComplex.cell (C i : Set K) 2) (a : UnitBoundary (Fin 2 → ℝ)) :
    subcomplexGraphDiskMap (hC hik) (rawAttaching C i ⟨j, a⟩) =
      rawAttaching C k ⟨subcomplexCellInclusion (hC hik) 2 j, a⟩ :=
  congrArg (fun f => f a) (subcomplexCellBoundary_natural (hC hik) j)

theorem wordAttaching_natural {i k : Fin (n + 1)} (hik : i ≤ k)
    (j : RelCWComplex.cell (C i : Set K) 2) (a : UnitBoundary (Fin 2 → ℝ)) :
    subcomplexGraphDiskMap (hC hik) (wordAttaching C hC i ⟨j, a⟩) =
      wordAttaching C hC k ⟨subcomplexCellInclusion (hC hik) 2 j, a⟩ := by
  change subcomplexGraphDiskMap _ ((word C hC i j).boundaryMap a) =
    (word C hC k _).boundaryMap a
  rw [word_natural C hC hik]
  exact congrArg (fun f => f a) (subcomplexBoundaryWord_map (hC hik) (word C hC i j))

def rawDiskInclusion {i k : Fin (n + 1)} (hik : i ≤ k) :
    C(DiskAttachment (rawAttaching C i), DiskAttachment (rawAttaching C k)) :=
  diskFamilyMap (rawAttaching C i) (rawAttaching C k) (subcomplexGraphDiskMap (hC hik))
    (subcomplexCellInclusion (hC hik) 2) (rawAttaching_natural K C hC hik)

def wordDiskInclusion {i k : Fin (n + 1)} (hik : i ≤ k) :
    C(DiskAttachment (wordAttaching C hC i), DiskAttachment (wordAttaching C hC k)) :=
  diskFamilyMap (wordAttaching C hC i) (wordAttaching C hC k)
    (subcomplexGraphDiskMap (hC hik)) (subcomplexCellInclusion (hC hik) 2)
    (wordAttaching_natural K C hC hik)

theorem wordDiskChange_natural {i k : Fin (n + 1)} (hik : i ≤ k) :
    (wordDiskInclusion K C hC hik).comp (wordDiskChange C hC i).toFun =
      (wordDiskChange C hC k).toFun.comp (rawDiskInclusion K C hC hik) :=
  naturalDiskAttachingEquiv_natural _ _ (attachingHomotopy C hC i)
    _ _ (attachingHomotopy C hC k) (subcomplexGraphDiskMap (hC hik))
    (subcomplexCellInclusion (hC hik) 2) (rawAttaching_natural K C hC hik)
    (wordAttaching_natural K C hC hik)
    (fun t j a => (attachingHomotopy_natural C hC hik j t a).symm)

def rawBaseChange (i : Fin (n + 1)) :=
  diskAttachmentBaseChangeHomotopyEquiv (skeletonAttachingMap (C i : Set K) 2)
    (skeletonAsDiskAttachment (C i : Set K) 1).toHomotopyEquiv

omit [Choices C] in
theorem rawBaseChange_natural {i k : Fin (n + 1)} (hik : i ≤ k) :
    (rawDiskInclusion K C hC hik).comp (rawBaseChange K C i).toFun =
      (rawBaseChange K C k).toFun.comp (subcomplexDiskMap (hC hik) 2) := by
  apply hom_ext (skeletonAttachingMap (C i : Set K) 2)
    (boundaryFamilyInclusion (RelCWComplex.cell (C i : Set K) 2) (Fin 2 → ℝ))
  · intro x
    change rawDiskInclusion K C hC hik
      (diskAttachmentBaseChangeHomotopyEquiv (skeletonAttachingMap (C i : Set K) 2)
        (skeletonAsDiskAttachment (C i : Set K) 1).toHomotopyEquiv
        (old (skeletonAttachingMap (C i : Set K) 2)
          (boundaryFamilyInclusion (RelCWComplex.cell (C i : Set K) 2) (Fin 2 → ℝ)) x)) = _
    rw [diskAttachmentBaseChangeHomotopyEquiv_old]
    change diskFamilyMap _ _ _ _ _ (old _ _ _) =
      diskAttachmentBaseChangeHomotopyEquiv _ _ (subcomplexDiskMap _ 2 (old _ _ x))
    rw [diskFamilyMap_old, subcomplexDiskMap_old, diskAttachmentBaseChangeHomotopyEquiv_old]
    congr 1
    change (skeletonAttachmentHomeomorph (C k : Set K) 1).symm
      (subcomplexSkeletonInclusion (hC hik) 2
        ((skeletonAttachmentHomeomorph (C i : Set K) 1)
          ((skeletonAttachmentHomeomorph (C i : Set K) 1).symm x))) = _
    rw [Homeomorph.apply_symm_apply]
    rfl
  · rintro ⟨j, x⟩
    change rawDiskInclusion K C hC hik (diskAttachmentBaseChangeHomotopyEquiv _ _ (cell _ _ ⟨j, x⟩)) = _
    rw [diskAttachmentBaseChangeHomotopyEquiv_cell]
    change diskFamilyMap _ _ _ _ _ (cell _ _ _) =
      diskAttachmentBaseChangeHomotopyEquiv _ _ (subcomplexDiskMap _ 2 (cell _ _ ⟨j, x⟩))
    rw [diskFamilyMap_cell, subcomplexDiskMap_cell, diskAttachmentBaseChangeHomotopyEquiv_cell]
    rfl

omit [Choices C] in
theorem rawDiskEquiv_natural {i k : Fin (n + 1)} (hik : i ≤ k) (x : (C i : Set K)) :
    rawDiskInclusion K C hC hik (rawDiskEquiv K C i x) =
      rawDiskEquiv K C k (Set.inclusion (hC hik) x) := by
  change rawDiskInclusion K C hC hik
      (rawBaseChange K C i (subcomplexAsDiskAttachment K (C i) x)) =
    rawBaseChange K C k (subcomplexAsDiskAttachment K (C k) (Set.inclusion (hC hik) x))
  rw [subcomplexAsDiskAttachment_natural K (hC hik) x]
  exact congrArg (fun f => f (subcomplexAsDiskAttachment K (C i) x))
    (rawBaseChange_natural K C hC hik)

theorem wordDiskEquiv_natural {i k : Fin (n + 1)} (hik : i ≤ k) :
    (wordDiskInclusion K C hC hik).comp (wordDiskEquiv K C hC i).toFun =
      (wordDiskEquiv K C hC k).toFun.comp
        ⟨Set.inclusion (hC hik), continuous_inclusion (hC hik)⟩ := by
  ext x
  change wordDiskInclusion K C hC hik (wordDiskChange C hC i (rawDiskEquiv K C i x)) = _
  have h := congrArg (fun f => f (rawDiskEquiv K C i x)) (wordDiskChange_natural K C hC hik)
  change wordDiskInclusion K C hC hik (wordDiskChange C hC i (rawDiskEquiv K C i x)) =
    wordDiskChange C hC k (rawDiskInclusion K C hC hik (rawDiskEquiv K C i x)) at h
  rw [h, rawDiskEquiv_natural]
  rfl

theorem wordDiskInclusion_killsPi2_iff {i k : Fin (n + 1)} (hik : i ≤ k) :
    Whitehead.KillsPi2 (wordDiskInclusion K C hC hik) ↔
      Whitehead.KillsPi2 (⟨Set.inclusion (hC hik), continuous_inclusion (hC hik)⟩ :
        C((C i : Set K), (C k : Set K))) := by
  apply Whitehead.killsPi2_homotopyEquiv_square_iff
    (wordDiskEquiv K C hC i) (wordDiskEquiv K C hC k)
  rw [wordDiskEquiv_natural]

end ChainWords
end FiniteChains.ClassicalCW
