import RequestProject.ClassicalCWGraphCoordinates
import RequestProject.ComponentComplex

/-! Original subcomplex inclusions induce compatible graph inclusions and
actual maps of disk models, retaining every original vertex and edge.
This is the simultaneous graph datum for necessity. Unverified source. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.ClassicalCW
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment
open Set Topology
open scoped Classical unitInterval

variable {X : Type} [TopologicalSpace X] [T2Space X] [CWComplex (Set.univ : Set X)]
  {C D E : CWComplex.Subcomplex (Set.univ : Set X)}

theorem subcomplex_cell_mono (h : (C : Set X) ⊆ D) (n : ℕ) : C.I n ⊆ D.I n := by
  intro j hj
  have hx := CWComplex.map_zero_mem_openCell (C := (Set.univ : Set X)) n j
  have hxD := h (C.openCell_subset_of_mem hj hx)
  by_contra hn
  exact Set.disjoint_left.mp (D.disjoint_openCell_subcomplex_of_not_mem hn) hx hxD

def subcomplexCellInclusion (h : (C : Set X) ⊆ D) (n : ℕ) :
    RelCWComplex.cell (C : Set X) n ↪ RelCWComplex.cell (D : Set X) n :=
  ⟨fun j => ⟨j.val, subcomplex_cell_mono h n j.property⟩,
    fun _ _ he => Subtype.ext (congrArg (fun z : RelCWComplex.cell (D : Set X) n => z.val) he)⟩

theorem subcomplex_skeleton_mono (h : (C : Set X) ⊆ D) (n : ℕ) :
    (CWComplex.skeletonLT (C : Set X) (n : ℕ∞) : Set X) ⊆
      CWComplex.skeletonLT (D : Set X) (n : ℕ∞) := by
  intro x hx
  rw [← CWComplex.iUnion_openCell_eq_skeletonLT] at hx ⊢
  obtain ⟨m, hm, j, hxj⟩ := by simpa only [Set.mem_iUnion] using hx
  exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hm,
    Set.mem_iUnion.mpr ⟨subcomplexCellInclusion h m j, hxj⟩⟩⟩

def subcomplexSkeletonInclusion (h : (C : Set X) ⊆ D) (n : ℕ) :
    C(SkeletonCarrier (C : Set X) n, SkeletonCarrier (D : Set X) n) :=
  ⟨fun x => ⟨x.val, subcomplex_skeleton_mono h n x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem subcomplexSkeletonInclusion_injective (h : (C : Set X) ⊆ D) (n : ℕ) :
    Function.Injective (subcomplexSkeletonInclusion h n) :=
  fun _ _ he => Subtype.ext (congrArg (fun z : SkeletonCarrier (D : Set X) n => z.val) he)

theorem subcomplexSkeletonInclusion_comp (h : (C : Set X) ⊆ D)
    (k : (D : Set X) ⊆ E) (n : ℕ) :
    (subcomplexSkeletonInclusion k n).comp (subcomplexSkeletonInclusion h n) =
      subcomplexSkeletonInclusion (h.trans k) n := by
  ext x
  rfl

def subcomplexGraph (C : CWComplex.Subcomplex (Set.univ : Set X)) : Comb.Complex2 :=
  graphCx (skeletonAttachingMap (C : Set X) 1)

def subcomplexGraphInclusion (h : (C : Set X) ⊆ D) :
    Comb.Hom (subcomplexGraph C) (subcomplexGraph D) where
  onV := subcomplexSkeletonInclusion h 1
  onE := subcomplexCellInclusion h 1
  onF := Empty.elim
  src_onE _ := Subtype.ext rfl
  tgt_onE _ := Subtype.ext rfl
  base_onF f := Empty.elim f
  att_onF f := Empty.elim f

theorem subcomplexGraphInclusion_injective_V (h : (C : Set X) ⊆ D) :
    Function.Injective (subcomplexGraphInclusion h).onV :=
  subcomplexSkeletonInclusion_injective h 1

theorem subcomplexGraphInclusion_injective_E (h : (C : Set X) ⊆ D) :
    Function.Injective (subcomplexGraphInclusion h).onE :=
  (subcomplexCellInclusion h 1).injective

theorem subcomplexGraphInclusion_comp (h : (C : Set X) ⊆ D)
    (k : (D : Set X) ⊆ E) :
    (subcomplexGraphInclusion k).comp (subcomplexGraphInclusion h) =
      subcomplexGraphInclusion (h.trans k) := by
  refine Comb.Hom.ext' ?_ ?_ ?_
  · rfl
  · rfl
  · funext f
    exact Empty.elim f

theorem subcomplexZeroSkeleton_discrete (C : CWComplex.Subcomplex (Set.univ : Set X)) :
    DiscreteTopology (SkeletonCarrier (C : Set X) 1) := by
  have hs : (CWComplex.skeletonLT (C : Set X) (1 : ℕ∞) : Set X) ⊆
      (CWComplex.skeletonLT (Set.univ : Set X) (1 : ℕ∞) : Set X) := by
    intro x hx
    rw [← CWComplex.iUnion_openCell_eq_skeletonLT] at hx ⊢
    obtain ⟨n, hn, j, hj⟩ := by simpa only [Set.mem_iUnion] using hx
    exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨hn,
      Set.mem_iUnion.mpr ⟨j.val, hj⟩⟩⟩
  exact ((zeroSkeleton_cellSeparated (X := X)).mono hs).isDiscrete.to_subtype

def subcomplexDiskMap (h : (C : Set X) ⊆ D) (n : ℕ) :
    C(DiskAttachment (skeletonAttachingMap (C : Set X) n),
      DiskAttachment (skeletonAttachingMap (D : Set X) n)) :=
  (⟨_, (skeletonAsDiskAttachment (D : Set X) n).continuous⟩ :
      C(SkeletonCarrier (D : Set X) (n + 1), _)).comp
    ((subcomplexSkeletonInclusion h (n + 1)).comp
      ⟨_, (skeletonAttachmentHomeomorph (C : Set X) n).continuous⟩)

theorem subcomplexDiskMap_skeleton (h : (C : Set X) ⊆ D) (n : ℕ)
    (z : DiskAttachment (skeletonAttachingMap (C : Set X) n)) :
    skeletonAttachmentHomeomorph (D : Set X) n (subcomplexDiskMap h n z) =
      subcomplexSkeletonInclusion h (n + 1) (skeletonAttachmentHomeomorph (C : Set X) n z) :=
  (skeletonAttachmentHomeomorph (D : Set X) n).apply_symm_apply _

theorem subcomplexDiskMap_old (h : (C : Set X) ⊆ D) (n : ℕ)
    (x : SkeletonCarrier (C : Set X) n) :
    subcomplexDiskMap h n (old (skeletonAttachingMap (C : Set X) n) _ x) =
      old (skeletonAttachingMap (D : Set X) n) _ (subcomplexSkeletonInclusion h n x) := by
  apply (skeletonAttachmentHomeomorph (D : Set X) n).injective
  rw [subcomplexDiskMap_skeleton]
  apply Subtype.ext
  rfl

theorem subcomplexDiskMap_cell (h : (C : Set X) ⊆ D) (n : ℕ)
    (j : RelCWComplex.cell (C : Set X) n) (x : ClosedUnitBall (Fin n → ℝ)) :
    subcomplexDiskMap h n (cell (skeletonAttachingMap (C : Set X) n) _ ⟨j, x⟩) =
      cell (skeletonAttachingMap (D : Set X) n) _ ⟨subcomplexCellInclusion h n j, x⟩ := by
  apply (skeletonAttachmentHomeomorph (D : Set X) n).injective
  rw [subcomplexDiskMap_skeleton]
  apply Subtype.ext
  change (skeletonAttachmentHomeomorph (C : Set X) n (cell _ _ ⟨j, x⟩)).val = _
  rw [skeletonAttachmentHomeomorph_cell, skeletonAttachmentHomeomorph_cell]
  rfl

def subcomplexGraphDiskMap (h : (C : Set X) ⊆ D) :
    C(DiskAttachment (skeletonAttachingMap (C : Set X) 1),
      DiskAttachment (skeletonAttachingMap (D : Set X) 1)) := subcomplexDiskMap h 1

theorem subcomplexGraphDiskMap_skeleton (h : (C : Set X) ⊆ D)
    (z : DiskAttachment (skeletonAttachingMap (C : Set X) 1)) :
    skeletonAttachmentHomeomorph (D : Set X) 1 (subcomplexGraphDiskMap h z) =
      subcomplexSkeletonInclusion h 2 (skeletonAttachmentHomeomorph (C : Set X) 1 z) :=
  (skeletonAttachmentHomeomorph (D : Set X) 1).apply_symm_apply _

theorem subcomplexGraphDiskMap_old (h : (C : Set X) ⊆ D)
    (v : (subcomplexGraph C).V) :
    subcomplexGraphDiskMap h
      (old (skeletonAttachingMap (C : Set X) 1) _ v) =
      old (skeletonAttachingMap (D : Set X) 1) _ ((subcomplexGraphInclusion h).onV v) := by
  apply (skeletonAttachmentHomeomorph (D : Set X) 1).injective
  rw [subcomplexGraphDiskMap_skeleton]
  apply Subtype.ext
  rfl

theorem subcomplexGraphDiskMap_edge (h : (C : Set X) ⊆ D)
    (j : (subcomplexGraph C).E) (t : I) :
    subcomplexGraphDiskMap h (graphEdgePath (skeletonAttachingMap (C : Set X) 1) j t) =
      graphEdgePath (skeletonAttachingMap (D : Set X) 1)
        ((subcomplexGraphInclusion h).onE j) t := by
  apply (skeletonAttachmentHomeomorph (D : Set X) 1).injective
  rw [subcomplexGraphDiskMap_skeleton]
  apply Subtype.ext
  change (skeletonAttachmentHomeomorph (C : Set X) 1
    (cell _ _ ⟨j, graphDiskHomeomorph t⟩)).val =
    (skeletonAttachmentHomeomorph (D : Set X) 1
      (cell _ _ ⟨subcomplexCellInclusion h 1 j, graphDiskHomeomorph t⟩)).val
  rw [skeletonAttachmentHomeomorph_cell, skeletonAttachmentHomeomorph_cell]
  rfl

theorem subcomplexGraphDiskMap_comp (h : (C : Set X) ⊆ D)
    (k : (D : Set X) ⊆ E) :
    (subcomplexGraphDiskMap k).comp (subcomplexGraphDiskMap h) =
      subcomplexGraphDiskMap (h.trans k) := by
  ext z
  apply (skeletonAttachmentHomeomorph (E : Set X) 1).injective
  change skeletonAttachmentHomeomorph (E : Set X) 1
    (subcomplexGraphDiskMap k (subcomplexGraphDiskMap h z)) =
    skeletonAttachmentHomeomorph (E : Set X) 1 (subcomplexGraphDiskMap (h.trans k) z)
  rw [subcomplexGraphDiskMap_skeleton, subcomplexGraphDiskMap_skeleton,
    subcomplexGraphDiskMap_skeleton]
  rfl

end FiniteChains.ClassicalCW
