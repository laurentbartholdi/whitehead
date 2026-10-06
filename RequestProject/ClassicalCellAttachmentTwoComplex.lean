import RequestProject.Statement
import RequestProject.ClassicalCellAttachmentCW
import Mathlib.Analysis.Normed.Module.Connected

/-! Disk attachments as the actual two-complexes of the challenge. The
old space is a closed subcomplex retaining precisely its original cells.
Finiteness is asserted only when both the old cells and new labels are finite. -/

noncomputable section
open scoped Classical Topology
open Set Topology Metric

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.RelativeAttachment

theorem closedUnitBall_connectedSpace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] : ConnectedSpace (ClosedUnitBall E) := by
  apply isConnected_iff_connectedSpace.mp
  convert isConnected_closedBall (E := E) (x := (0 : E)) (r := (1 : ℝ)) zero_le_one using 1
  ext x
  simp only [Metric.mem_closedBall, dist_zero_right]
  rfl

/-- Every new disk meets the old connected space along its nonempty
boundary. This holds for arbitrary, possibly infinite families of disks. -/
theorem diskAttachment_connectedSpace {X J E : Type}
    [TopologicalSpace X] [ConnectedSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : BoundaryFamily J E → X) (a : UnitBoundary E) :
    ConnectedSpace (DiskAttachment r) := by
  letI := closedUnitBall_connectedSpace (E := E)
  let x₀ : X := Classical.choice inferInstance
  let o := old r (boundaryFamilyInclusion J E)
  have ho : Set.range o ⊆ connectedComponent (o x₀) :=
    (isConnected_range (old_continuous r _)).subset_connectedComponent ⟨x₀, rfl⟩
  apply connectedSpace_iff_connectedComponent.mpr
  refine ⟨o x₀, Set.eq_univ_of_forall ?_⟩
  rintro (x | d)
  · exact ho ⟨x, rfl⟩
  · let f : ClosedUnitBall E → DiskAttachment r :=
      fun v => cell r (boundaryFamilyInclusion J E) ⟨d.val.1, v⟩
    have hf : Continuous f := (cell_continuous r _).comp continuous_sigmaMk
    have hb : f (unitBoundaryInclusion E a) = o (r ⟨d.val.1, a⟩) :=
      cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J E).injective
        ⟨d.val.1, a⟩
    have hc : Sum.inr d ∈ connectedComponent (o (r ⟨d.val.1, a⟩)) :=
      (isConnected_range hf).subset_connectedComponent
        ⟨unitBoundaryInclusion E a, hb⟩
        ⟨d.val.2, cell_of_not_mem r _ d.val d.property⟩
    rw [connectedComponent_eq (ho ⟨r ⟨d.val.1, a⟩, rfl⟩)]
    exact hc

/-- A distinguished boundary point for every positive-dimensional disk,
using the same sup norm as the original classical CW characteristic maps. -/
def positiveDiskBoundaryPoint (n : ℕ) (hn : 0 < n) : UnitBoundary (Fin n → ℝ) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ⟨fun _ => 1, by simp [pi_norm_const]⟩

variable {X J : Type} [TopologicalSpace X] [T2Space X] [Nonempty X]
  [CWComplex (Set.univ : Set X)]

/-- Count all old cells once and all new cells once. In particular there
is no finiteness assumption on the dimension index itself. -/
def attachmentTotalCellEquiv (n : ℕ) :
    (Σ m, AttachmentCell (X := X) (J := J) n m) ≃
      (Σ m, RelCWComplex.cell (Set.univ : Set X) m) ⊕ J where
  toFun
    | ⟨m, Sum.inl j⟩ => Sum.inl ⟨m, j⟩
    | ⟨_, Sum.inr j⟩ => Sum.inr j.val
  invFun
    | Sum.inl ⟨m, j⟩ => ⟨m, Sum.inl j⟩
    | Sum.inr j => ⟨n, Sum.inr ⟨j, rfl⟩⟩
  left_inv := by
    rintro ⟨m, j | ⟨j, h⟩⟩
    · rfl
    · subst m
      rfl
  right_inv := by rintro (⟨m, j⟩ | j) <;> rfl

end FiniteChains.RelativeAttachment

namespace Whitehead
open FiniteChains.RelativeAttachment

variable (K : TwoComplex) {J : Type} (n : ℕ) (hn : 0 < n) (hn₂ : n ≤ 2)
  (r : C(BoundaryFamily J (Fin n → ℝ), K)) (x₀ : K)
  (hb : FiniteLowerBoundary n r)

/-- The extension is built directly on the original space, retaining its
old cells and adding only the specified one- or two-dimensional disks. -/
def diskAttachmentTwoComplex : TwoComplex where
  space := DiskAttachment r
  topology := inferInstance
  hausdorff := diskAttachment_t2Space r r.continuous
  cw := attachmentCW n r r.continuous x₀ hb
  connected := diskAttachment_connectedSpace r (positiveDiskBoundaryPoint n hn)
  dimension m hm := ⟨by
    intro j
    change AttachmentCell (X := K) (J := J) n m at j
    rcases j with j | ⟨j, h⟩
    · exact (K.dimension m hm).false j
    · omega⟩

def diskAttachmentOldSubcomplex :
    CWComplex.Subcomplex (Set.univ : Set (diskAttachmentTwoComplex K n hn hn₂ r x₀ hb)) :=
  attachmentOldSubcomplex n r r.continuous x₀ hb

def diskAttachmentOldHomeomorph :
    K ≃ₜ (diskAttachmentOldSubcomplex K n hn hn₂ r x₀ hb :
      Set (diskAttachmentTwoComplex K n hn hn₂ r x₀ hb)) :=
  (old_isClosedEmbedding r _ r.continuous
    (boundaryFamilyInclusion_isClosedEmbedding J (Fin n → ℝ))).isEmbedding.toHomeomorph

/-- The initial identification is literal on the given open cells, not
merely an identification of a homotopy type with a presentation model. -/
theorem diskAttachment_initialIdentification :
    InitialIdentification (diskAttachmentOldSubcomplex K n hn hn₂ r x₀ hb)
      (diskAttachmentOldHomeomorph K n hn hn₂ r x₀ hb) := by
  intro m
  refine ⟨attachmentOldCellEquiv (X := K) (J := J) n m, ?_⟩
  intro j
  exact attachment_old_openCell n r r.continuous x₀ hb m j

theorem diskAttachment_finiteCells (hK : FiniteCells K) [Finite J] :
    FiniteCells (diskAttachmentTwoComplex K n hn hn₂ r x₀ hb) := by
  letI : Finite (Σ m, RelCWComplex.cell (Set.univ : Set K) m) := hK
  change Finite (Σ m, AttachmentCell (X := K) (J := J) n m)
  exact Finite.of_injective (attachmentTotalCellEquiv (X := K) (J := J) n)
    (attachmentTotalCellEquiv (X := K) (J := J) n).injective

theorem diskAttachment_old_connectedSpace :
    ConnectedSpace (diskAttachmentOldSubcomplex K n hn hn₂ r x₀ hb :
      Set (diskAttachmentTwoComplex K n hn hn₂ r x₀ hb)) :=
  (diskAttachmentOldHomeomorph K n hn hn₂ r x₀ hb).surjective.connectedSpace
    (diskAttachmentOldHomeomorph K n hn hn₂ r x₀ hb).continuous

/-- A nonempty attached family makes the old subcomplex proper. The
witness is the center of any added disk. -/
theorem diskAttachment_old_ne_univ [Nonempty J] :
    (diskAttachmentOldSubcomplex K n hn hn₂ r x₀ hb :
      Set (diskAttachmentTwoComplex K n hn hn₂ r x₀ hb)) ≠ Set.univ := by
  let j : J := Classical.choice inferInstance
  let d := interiorDiskPoint (E := Fin n → ℝ) j ⟨0, by simp⟩
  intro h
  have hd : fresh r (boundaryFamilyInclusion J (Fin n → ℝ)) d ∈
      (diskAttachmentOldSubcomplex K n hn hn₂ r x₀ hb :
        Set (diskAttachmentTwoComplex K n hn hn₂ r x₀ hb)) := by
    rw [h]
    trivial
  obtain ⟨x, hx⟩ := hd
  exact Sum.inl_ne_inr hx

end Whitehead
