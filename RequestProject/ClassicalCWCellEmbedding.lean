module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.ClassicalCellAttachmentTwoComplex
public import RequestProject.TopologicalPi2HomotopyTransport

@[expose] public section

/-! Closed embeddings retaining the actual open cells of classical CW
complexes. Compatible embeddings into a final stage give the exact chain
predicate, including its original-cell identification. -/

noncomputable section
namespace Whitehead
open Topology

structure CWCellEmbedding (K L : TwoComplex) where
  map : C(K, L)
  closedEmbedding : IsClosedEmbedding map
  cellIndex : ∀ m, RelCWComplex.cell (Set.univ : Set K) m ↪
    RelCWComplex.cell (Set.univ : Set L) m
  openCell_image : ∀ m j,
    map '' CWComplex.openCell (C := (Set.univ : Set K)) m j =
      CWComplex.openCell (C := (Set.univ : Set L)) m (cellIndex m j)

namespace CWCellEmbedding

variable {K L M : TwoComplex}

def refl (K : TwoComplex) : CWCellEmbedding K K where
  map := ContinuousMap.id K
  closedEmbedding := IsClosedEmbedding.id
  cellIndex _ := Function.Embedding.refl _
  openCell_image _ _ := Set.image_id _

def comp (g : CWCellEmbedding L M) (f : CWCellEmbedding K L) : CWCellEmbedding K M where
  map := g.map.comp f.map
  closedEmbedding := g.closedEmbedding.comp f.closedEmbedding
  cellIndex m := (f.cellIndex m).trans (g.cellIndex m)
  openCell_image m j := by
    change (g.map ∘ f.map) '' _ = _
    rw [Set.image_comp, f.openCell_image, g.openCell_image]
    rfl

/-- The image has the CW subcomplex structure specified by the actual
cell images, not by a separately chosen CW decomposition of the range. -/
def imageSubcomplex (e : CWCellEmbedding K L) : CWComplex.Subcomplex (Set.univ : Set L) where
  carrier := Set.range e.map
  I m := Set.range (e.cellIndex m)
  closed' := e.closedEmbedding.isClosed_range
  union' := by
    rw [Set.empty_union]
    ext z
    constructor
    · intro hz
      obtain ⟨m, ⟨j, hj⟩, hz⟩ := by simpa only [Set.mem_iUnion] using hz
      obtain ⟨j, rfl⟩ := hj
      rw [← e.openCell_image] at hz
      exact Set.image_subset_range _ _ hz
    · rintro ⟨x, rfl⟩
      have hx : x ∈ ⋃ m, ⋃ j : RelCWComplex.cell (Set.univ : Set K) m,
          CWComplex.openCell (C := (Set.univ : Set K)) m j := by
        rw [CWComplex.iUnion_openCell_eq_complex]
        trivial
      obtain ⟨m, j, hj⟩ := by simpa only [Set.mem_iUnion] using hx
      apply Set.mem_iUnion.mpr
      refine ⟨m, Set.mem_iUnion.mpr ⟨⟨e.cellIndex m j, ⟨j, rfl⟩⟩, ?_⟩⟩
      rw [← e.openCell_image]
      exact ⟨x, hj, rfl⟩

def imageHomeomorph (e : CWCellEmbedding K L) : K ≃ₜ (e.imageSubcomplex : Set L) :=
  e.closedEmbedding.isEmbedding.toHomeomorph

@[simp] theorem imageHomeomorph_val (e : CWCellEmbedding K L) (x : K) :
    (e.imageHomeomorph x).val = e.map x := rfl

def imageCellEquiv (e : CWCellEmbedding K L) (m : ℕ) :
    RelCWComplex.cell (Set.univ : Set K) m ≃
      {j : RelCWComplex.cell (Set.univ : Set L) m // j ∈ e.imageSubcomplex.I m} :=
  Equiv.ofInjective (e.cellIndex m) (e.cellIndex m).injective

theorem initialIdentification (e : CWCellEmbedding K L) :
    InitialIdentification e.imageSubcomplex e.imageHomeomorph := by
  intro m
  exact ⟨e.imageCellEquiv m, e.openCell_image m⟩

theorem image_connectedSpace (e : CWCellEmbedding K L) :
    ConnectedSpace (e.imageSubcomplex : Set L) :=
  e.imageHomeomorph.surjective.connectedSpace e.imageHomeomorph.continuous

end CWCellEmbedding

/-- Each actual cellular disk extension supplies a closed embedding
retaining every original cell, for use in subsequent extensions. -/
def diskAttachmentCellEmbedding (K : TwoComplex) {J : Type}
    (n : ℕ) (hn : 0 < n) (hn₂ : n ≤ 2)
    (r : C(FiniteChains.RelativeAttachment.BoundaryFamily J (Fin n → ℝ), K)) (x₀ : K)
    (hb : FiniteChains.RelativeAttachment.FiniteLowerBoundary n r) :
    CWCellEmbedding K (diskAttachmentTwoComplex K n hn hn₂ r x₀ hb) where
  map := ⟨FiniteChains.RelativeAttachment.old r
    (FiniteChains.RelativeAttachment.boundaryFamilyInclusion J (Fin n → ℝ)),
    FiniteChains.RelativeAttachment.old_continuous _ _⟩
  closedEmbedding := FiniteChains.RelativeAttachment.old_isClosedEmbedding r _ r.continuous
    (FiniteChains.RelativeAttachment.boundaryFamilyInclusion_isClosedEmbedding J (Fin n → ℝ))
  cellIndex _ := ⟨Sum.inl, Sum.inl_injective⟩
  openCell_image :=
    FiniteChains.RelativeAttachment.attachment_old_openCell n r r.continuous x₀ hb

/-- A finite compatible family of embeddings yields the original chain
statement in the chosen common ambient two-complex. -/
theorem hasChain_of_cellEmbeddings {n : ℕ} (K : Fin (n + 1) → TwoComplex) (L : TwoComplex)
    (e : ∀ i, CWCellEmbedding (K i) L)
    (f : ∀ i : Fin n, C(K i.castSucc, K i.succ))
    (he : ∀ i : Fin n, (e i.succ).map.comp (f i) = (e i.castSucc).map)
    (hp : ∀ i : Fin n, ∃ x : K i.succ, (e i.succ).map x ∉ Set.range (e i.castSucc).map)
    (hk : ∀ i : Fin n, KillsPi2 (f i))
    (finite : Bool) (hfin : finite = true → FiniteCells L) :
    HasChain (K 0) n finite := by
  refine ⟨L, fun i => (e i).imageSubcomplex, (e 0).imageHomeomorph,
    (e 0).initialIdentification, hfin, fun i => (e i).image_connectedSpace, ?_⟩
  intro i
  have hs : Set.range (e i.castSucc).map ⊆ Set.range (e i.succ).map := by
    rintro _ ⟨x, rfl⟩
    exact ⟨f i x, congrArg (fun g : C(K i.castSucc, L) => g x) (he i)⟩
  refine ⟨hs, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hp i
    intro heq
    apply hx
    change Set.range (e i.castSucc).map = Set.range (e i.succ).map at heq
    rw [heq]
    exact ⟨x, rfl⟩
  · apply (killsPi2_homotopyEquiv_square_iff
      (e i.castSucc).imageHomeomorph.toHomotopyEquiv
      (e i.succ).imageHomeomorph.toHomotopyEquiv (f i)
      ⟨Set.inclusion hs, continuous_inclusion hs⟩ ?_).mpr (hk i)
    have hsq :
        (⟨Set.inclusion hs, continuous_inclusion hs⟩ :
          C(((e i.castSucc).imageSubcomplex : Set L),
            ((e i.succ).imageSubcomplex : Set L))).comp
            (e i.castSucc).imageHomeomorph.toContinuousMap =
        (e i.succ).imageHomeomorph.toContinuousMap.comp (f i) := by
      apply ContinuousMap.ext
      intro x
      apply Subtype.ext
      exact (congrArg (fun g : C(K i.castSucc, L) => g x) (he i)).symm
    exact hsq ▸ ContinuousMap.Homotopic.refl _

end Whitehead
