import RequestProject.ClassicalCWLoopCellularization
import RequestProject.ClassicalGraphPathStraightening
import Mathlib.Topology.Connected.Clopen

/-! The actual graph underlying the original CW one-skeleton. Its vertices
are the literal zero-skeleton points and its edges the original one-cell
indices. Connectedness and finite edge-word representatives are proved from
the original CW axioms. Pending Lean verification. -/

noncomputable section
open scoped Classical
open Set Topology

namespace FiniteChains.ClassicalCW
open ClassicalSkeletonAttachment RelativeAttachment ClassicalGraphModel ContinuousEdgeWords

variable {X : Type} [TopologicalSpace X] [T2Space X] [CWComplex (Set.univ : Set X)]

private theorem isClosed_of_closedCell_constant (S : Set X)
    (hS : ∀ n (j : RelCWComplex.cell (Set.univ : Set X) n),
      CWComplex.closedCell n j ⊆ S ∨ Disjoint (CWComplex.closedCell n j) S) : IsClosed S := by
  apply (CWComplex.closed (Set.univ : Set X) S (Set.subset_univ _)).mpr
  intro n j
  rcases hS n j with h | h
  · rw [Set.inter_eq_right.mpr h]
    exact CWComplex.isClosed_closedCell
  · rw [Set.disjoint_iff_inter_eq_empty.mp h.symm]
    exact isClosed_empty

theorem cw_pathComponent_isClopen (x : X) : IsClopen (pathComponent x) := by
  have hcell (n : ℕ) (j : RelCWComplex.cell (Set.univ : Set X) n) :
      CWComplex.closedCell n j ⊆ pathComponent x ∨
        Disjoint (CWComplex.closedCell n j) (pathComponent x) := by
    by_cases h : (CWComplex.closedCell n j ∩ pathComponent x).Nonempty
    · obtain ⟨y, hy, hxy⟩ := h
      left
      intro z hz
      exact hxy.trans ((closedCell_joined n j hy hz).joined)
    · exact Or.inr (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp h))
  refine ⟨isClosed_of_closedCell_constant (pathComponent x) hcell, ?_⟩
  apply isClosed_compl_iff.mp
  apply isClosed_of_closedCell_constant
  intro n j
  rcases hcell n j with h | h
  · right
    exact Set.disjoint_left.mpr (fun _ hy hz => hz (h hy))
  · left
    intro y hy hz
    exact Set.disjoint_left.mp h hy hz

/-- Connected classical CW complexes are actually path connected. -/
theorem cw_pathConnectedSpace [ConnectedSpace X] : PathConnectedSpace X where
  nonempty := inferInstance
  joined x y := by
    have h := (cw_pathComponent_isClopen x).eq_univ (pathComponent.nonempty x)
    exact (show y ∈ pathComponent x from by rw [h]; trivial)

theorem zeroSkeleton_cellSeparated :
    CellSeparated (CWComplex.skeletonLT (Set.univ : Set X) (1 : ℕ∞) : Set X) := by
  intro n j
  by_cases hn : n = 0
  · subst n
    exact (Set.subsingleton_singleton (a := RelCWComplex.map 0 j ![])).anti (by
      intro x hx
      simpa only [CWComplex.openCell_zero_eq_singleton] using hx.2)
  · intro x hx y hy
    exact False.elim (Set.disjoint_left.mp
      (CWComplex.disjoint_skeletonLT_openCell (C := (Set.univ : Set X)) (j := j)
        (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)) hx.1 hx.2)

theorem zeroSkeleton_discrete :
    DiscreteTopology (SkeletonCarrier (Set.univ : Set X) 1) :=
  (zeroSkeleton_cellSeparated (X := X)).isDiscrete.to_subtype

def zeroCellPoint (j : RelCWComplex.cell (Set.univ : Set X) 0) :
    SkeletonCarrier (Set.univ : Set X) 1 :=
  ⟨vertexPoint j, CWComplex.closedCell_subset_skeletonLT 0 j
    (by rw [CWComplex.closedCell_zero_eq_singleton]; rfl)⟩

theorem zeroCellPoint_bijective : Function.Bijective (zeroCellPoint (X := X)) := by
  constructor
  · intro i j h
    have hi : vertexPoint i ∈ CWComplex.openCell 0 i := by
      rw [CWComplex.openCell_zero_eq_singleton]
      rfl
    have hj : vertexPoint i ∈ CWComplex.openCell 0 j := by
      have hv : vertexPoint i = vertexPoint j := congrArg Subtype.val h
      rw [hv, CWComplex.openCell_zero_eq_singleton]
      rfl
    have hlabel := RelCWComplex.eq_of_not_disjoint_openCell
      (fun hd => Set.disjoint_left.mp hd hi hj)
    exact eq_of_heq (Sigma.mk.inj_iff.mp hlabel).2
  · intro x
    have hx := x.property
    change x.val ∈ (CWComplex.skeletonLT (Set.univ : Set X) (1 : ℕ∞) : Set X) at hx
    rw [← CWComplex.iUnion_openCell_eq_skeletonLT] at hx
    obtain ⟨n, hn, j, hj⟩ := by simpa only [Set.mem_iUnion] using hx
    have hn' : n < 1 := by exact_mod_cast hn
    have hn0 : n = 0 := by omega
    subst n
    refine ⟨j, Subtype.ext ?_⟩
    exact (show x.val = vertexPoint j from by
      simpa only [CWComplex.openCell_zero_eq_singleton, Set.mem_singleton_iff, vertexPoint] using hj).symm

/-- The literal original zero-cells label the vertices bijectively. -/
def zeroCellEquiv : RelCWComplex.cell (Set.univ : Set X) 0 ≃
    SkeletonCarrier (Set.univ : Set X) 1 :=
  Equiv.ofBijective zeroCellPoint zeroCellPoint_bijective

variable (K : Whitehead.TwoComplex)

theorem oneSkeleton_nonempty : Nonempty (OneSkeleton K) := by
  let x : K := Classical.choice inferInstance
  let j := pointVertex x
  exact ⟨skeletonInclusion (Set.univ : Set K) 1 (zeroCellPoint j)⟩

theorem oneSkeleton_pathConnectedSpace : PathConnectedSpace (OneSkeleton K) where
  nonempty := oneSkeleton_nonempty K
  joined x y := by
    letI := cw_pathConnectedSpace (X := K)
    obtain ⟨p⟩ := PathConnectedSpace.joined x.val y.val
    obtain ⟨q, _⟩ := path_into_oneSkeleton K x y p
    exact ⟨q⟩

abbrev originalGraphAttaching := skeletonAttachingMap (Set.univ : Set K) 1

def originalGraph : Comb.Complex2 := graphCx (originalGraphAttaching K)

theorem originalGraph_isConnected : Comb.IsConnected (originalGraph K) := by
  letI := zeroSkeleton_discrete (X := K)
  letI : PathConnectedSpace (SkeletonCarrier (Set.univ : Set K) 2) :=
    oneSkeleton_pathConnectedSpace K
  let e := skeletonAsDiskAttachment (Set.univ : Set K) 1
  letI : PathConnectedSpace (DiskAttachment (originalGraphAttaching K)) :=
    e.surjective.pathConnectedSpace e.continuous
  exact graphCx_isConnected (originalGraphAttaching K) (originalGraphAttaching K).continuous

/-- The original graph admits a spanning tree, including for arbitrary
infinite cell families. Its existence uses actual continuous connectedness. -/
theorem originalGraph_exists_spanningTree (v : SkeletonCarrier (Set.univ : Set K) 1) :
    ∃ T : Comb.SpanningTree (originalGraph K), T.root = v :=
  Comb.SpanningTree.exists_of_isConnected (originalGraph_isConnected K) v

theorem originalGraph_path_isWord (v w : SkeletonCarrier (Set.univ : Set K) 1)
    (p : Path (skeletonInclusion (Set.univ : Set K) 1 v)
      (skeletonInclusion (Set.univ : Set K) 1 w)) :
    ∃ l, ∃ hl : Comb.IsPath (originalGraph K).src (originalGraph K).tgt l v w,
      Path.Homotopic p
        (((realize (originalGraph K).src (originalGraph K).tgt
          (old (originalGraphAttaching K)
            (boundaryFamilyInclusion (RelCWComplex.cell (Set.univ : Set K) 1) (Fin 1 → ℝ)))
          (graphEdgePath (originalGraphAttaching K)) l hl).map
            (skeletonAttachmentHomeomorph (Set.univ : Set K) 1).continuous).cast
              (skeletonAttachmentHomeomorph_old_eq (Set.univ : Set K) 1 v).symm
              (skeletonAttachmentHomeomorph_old_eq (Set.univ : Set K) 1 w).symm) := by
  letI := zeroSkeleton_discrete (X := K)
  let e := skeletonAsDiskAttachment (Set.univ : Set K) 1
  let P := (p.map e.continuous).cast
    (skeletonAsDiskAttachment_inclusion (Set.univ : Set K) 1 v).symm
    (skeletonAsDiskAttachment_inclusion (Set.univ : Set K) 1 w).symm
  obtain ⟨l, hl, h⟩ := graph_path_isWord (originalGraphAttaching K)
    (originalGraphAttaching K).continuous v w P
  refine ⟨l, hl, ?_⟩
  have H := (h.map ⟨_, (skeletonAttachmentHomeomorph (Set.univ : Set K) 1).continuous⟩).pathCast
    (skeletonAttachmentHomeomorph_old_eq (Set.univ : Set K) 1 v).symm
    (skeletonAttachmentHomeomorph_old_eq (Set.univ : Set K) 1 w).symm
  have he : ((P.map (skeletonAttachmentHomeomorph (Set.univ : Set K) 1).continuous).cast
      (skeletonAttachmentHomeomorph_old_eq (Set.univ : Set K) 1 v).symm
      (skeletonAttachmentHomeomorph_old_eq (Set.univ : Set K) 1 w).symm) = p := by
    apply Path.ext
    funext t
    exact (skeletonAttachmentHomeomorph (Set.univ : Set K) 1).apply_symm_apply (p t)
  rwa [he] at H

end FiniteChains.ClassicalCW
