module

public import RequestProject.Statement
public import RequestProject.ClassicalCWVertexPaths
public import RequestProject.ClassicalCWCompactSupport
public import RequestProject.ClassicalCWSkeletonAttachment
public import RequestProject.DiskAttachmentRadialCore

@[expose] public section

/-! Actual paths and loops in the given two-dimensional CW complex can be
moved, relative to endpoints already in its one-skeleton, into that original
one-skeleton. The conclusion retains the original space and cells.
Pending Lean verification. -/

noncomputable section
open scoped Classical
open Set Topology

namespace FiniteChains.ClassicalCW
open ClassicalSkeletonAttachment RelativeAttachment

def OneSkeleton (K : Whitehead.TwoComplex) := SkeletonCarrier (Set.univ : Set K) 2

instance (K : Whitehead.TwoComplex) : TopologicalSpace (OneSkeleton K) :=
  inferInstanceAs (TopologicalSpace (SkeletonCarrier (Set.univ : Set K) 2))

theorem twoComplex_mem_skeleton_three (K : Whitehead.TwoComplex) (x : K) :
    x ∈ CWComplex.skeletonLT (Set.univ : Set K) (3 : ℕ∞) := by
  have hx : x ∈ ⋃ n, ⋃ j : RelCWComplex.cell (Set.univ : Set K) n,
      CWComplex.closedCell n j := by rw [CWComplex.union]; trivial
  obtain ⟨n, j, hj⟩ := by simpa only [Set.mem_iUnion] using hx
  have hn : n ≤ 2 := by
    by_contra h
    letI := K.dimension n (Nat.lt_of_not_ge h)
    exact isEmptyElim j
  exact CWComplex.skeletonLT_mono (C := (Set.univ : Set K))
    (show (n : ℕ∞) + 1 ≤ 3 by exact_mod_cast (by omega : n + 1 ≤ 3))
    (CWComplex.closedCell_subset_skeletonLT n j hj)

theorem twoComplex_skeleton_three (K : Whitehead.TwoComplex) :
    (CWComplex.skeletonLT (Set.univ : Set K) (3 : ℕ∞) : Set K) = Set.univ :=
  Set.eq_univ_of_forall (twoComplex_mem_skeleton_three K)

/-- Every path between original one-skeleton points is homotopic to a
path entirely in that original one-skeleton, fixing both endpoints. -/
theorem path_into_oneSkeleton (K : Whitehead.TwoComplex) (x y : OneSkeleton K)
    (p : Path x.val y.val) :
    ∃ q : Path x y, Path.Homotopic p (q.map continuous_subtype_val) := by
  let P : Path (skeletonInclusion (Set.univ : Set K) 2 x)
      (skeletonInclusion (Set.univ : Set K) 2 y) := {
    toFun := fun t => ⟨p t, twoComplex_mem_skeleton_three K (p t)⟩
    continuous_toFun := p.continuous.subtype_mk _
    source' := Subtype.ext p.source
    target' := Subtype.ext p.target }
  let e := skeletonAsDiskAttachment (Set.univ : Set K) 2
  let r := skeletonAttachingMap (Set.univ : Set K) 2
  let P' := (P.map e.continuous).cast
    (skeletonAsDiskAttachment_inclusion (Set.univ : Set K) 2 x).symm
    (skeletonAsDiskAttachment_inclusion (Set.univ : Set K) 2 y).symm
  obtain ⟨q, hq⟩ := twoCellAttachment_path_into_old r r.continuous x y P'
  refine ⟨q, ?_⟩
  have h := hq.map (skeletonAttachmentOrigin (Set.univ : Set K) 2)
  have hleft : P'.map (skeletonAttachmentOrigin (Set.univ : Set K) 2).continuous = p := by
    apply Path.ext
    funext t
    change (skeletonAttachmentHomeomorph (Set.univ : Set K) 2
      ((skeletonAttachmentHomeomorph (Set.univ : Set K) 2).symm (P t))).val = p t
    rw [Homeomorph.apply_symm_apply]
    rfl
  have hright : (q.map (old_continuous r
      (boundaryFamilyInclusion (RelCWComplex.cell (Set.univ : Set K) 2) (Fin 2 → ℝ)))).map
        (skeletonAttachmentOrigin (Set.univ : Set K) 2).continuous =
      q.map continuous_subtype_val := by
    apply Path.ext
    funext t
    rfl
  rwa [hleft, hright] at h

/-- The cellular representative has actual finite support in original
zero- and one-cells, even when the original CW complex is infinite. -/
theorem path_into_oneSkeleton_finite (K : Whitehead.TwoComplex) (x y : OneSkeleton K)
    (p : Path x.val y.val) :
    ∃ q : Path x y, Path.Homotopic p (q.map continuous_subtype_val) ∧
      ∃ I : ∀ m, Finset (RelCWComplex.cell (Set.univ : Set K) m),
        Set.range (q.map continuous_subtype_val) ⊆
          ⋃ (m < 2) (j ∈ I m), CWComplex.closedCell m j := by
  obtain ⟨q, hq⟩ := path_into_oneSkeleton K x y p
  refine ⟨q, hq, ?_⟩
  exact IsCompact.finite_lower_support (isCompact_range (q.map continuous_subtype_val).continuous) 2
    (by rintro _ ⟨t, rfl⟩; exact (q t).property)

end FiniteChains.ClassicalCW
