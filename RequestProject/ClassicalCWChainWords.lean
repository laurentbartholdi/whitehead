module

public import RequestProject.ClassicalSubcomplexBoundaryWords

@[expose] public section

/-! Simultaneous original-cell words for a finite filtration. Each actual
two-cell is straightened exactly once, at its first stage. The later
words, bases, and attaching homotopies are transported from this choice.
There is no finite-cell hypothesis. Unverified source. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment
open Set Topology
open scoped Classical
variable {X : Type} [TopologicalSpace X] [T2Space X] [CWComplex (Set.univ : Set X)]
  {n : ℕ} (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set X))
  (hC : Monotone C)

/-- Actual circle words and their homotopies. A seeded relative construction
may prescribe these on C0; the default is supplied by graph cellularization. -/
class Choices where
  cellWord : ∀ (i : Fin (n + 1)) (_j : RelCWComplex.cell (C i : Set X) 2),
    BoundaryWords (skeletonAttachingMap (C i : Set X) 1)
  cellWord_spec : ∀ i j,
    (subcomplexCellBoundary (C i) j).Homotopic (cellWord i j).boundaryMap

noncomputable instance (priority := low) defaultChoices : Choices C where
  cellWord i j := Classical.choose (subcomplexCellBoundary_word_exists (C i) j)
  cellWord_spec i j := Classical.choose_spec (subcomplexCellBoundary_word_exists (C i) j)

abbrev TopCell := RelCWComplex.cell (C (Fin.last n) : Set X) 2

def topCell (i : Fin (n + 1)) (j : RelCWComplex.cell (C i : Set X) 2) : TopCell C :=
  subcomplexCellInclusion (hC (Fin.le_last i)) 2 j

def birthSet (j : TopCell C) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => j.val ∈ (C i).I 2)

theorem birthSet_nonempty (j : TopCell C) : (birthSet C j).Nonempty :=
  ⟨Fin.last n, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.property⟩⟩

def birth (j : TopCell C) : Fin (n + 1) := (birthSet C j).min' (birthSet_nonempty C j)

theorem birth_mem (j : TopCell C) : j.val ∈ (C (birth C j)).I 2 :=
  (Finset.mem_filter.mp (Finset.min'_mem (birthSet C j) (birthSet_nonempty C j))).2

theorem birth_le (j : TopCell C) (i : Fin (n + 1)) (hj : j.val ∈ (C i).I 2) :
    birth C j ≤ i :=
  Finset.min'_le (birthSet C j) i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)

def birthCell (j : TopCell C) : RelCWComplex.cell (C (birth C j) : Set X) 2 :=
  ⟨j.val, birth_mem C j⟩

variable [Choices C]

def birthWord (j : TopCell C) : BoundaryWords (skeletonAttachingMap (C (birth C j) : Set X) 1) :=
  Choices.cellWord (birth C j) (birthCell C j)

theorem birthWord_spec (j : TopCell C) :
    (subcomplexCellBoundary (C (birth C j)) (birthCell C j)).Homotopic
      (birthWord C j).boundaryMap :=
  Choices.cellWord_spec (birth C j) (birthCell C j)

def word (i : Fin (n + 1)) (j : RelCWComplex.cell (C i : Set X) 2) :
    BoundaryWords (skeletonAttachingMap (C i : Set X) 1) :=
  (birthWord C (topCell C hC i j)).map
    (subcomplexGraphInclusion (hC (birth_le C (topCell C hC i j) i j.property)))

theorem word_spec (i : Fin (n + 1)) (j : RelCWComplex.cell (C i : Set X) 2) :
    (subcomplexCellBoundary (C i) j).Homotopic (word C hC i j).boundaryMap := by
  have H := subcomplexCellBoundary_word_transport
    (hC (birth_le C (topCell C hC i j) i j.property))
    (birthCell C (topCell C hC i j)) (birthWord C (topCell C hC i j))
    (birthWord_spec C (topCell C hC i j))
  have he : subcomplexCellInclusion
      (hC (birth_le C (topCell C hC i j) i j.property)) 2
      (birthCell C (topCell C hC i j)) = j := Subtype.ext rfl
  rwa [he] at H

omit [Choices C] in
theorem topCell_natural {i k : Fin (n + 1)} (hik : i ≤ k)
    (j : RelCWComplex.cell (C i : Set X) 2) :
    topCell C hC k (subcomplexCellInclusion (hC hik) 2 j) = topCell C hC i j :=
  Subtype.ext rfl

theorem word_natural {i k : Fin (n + 1)} (hik : i ≤ k)
    (j : RelCWComplex.cell (C i : Set X) 2) :
    word C hC k (subcomplexCellInclusion (hC hik) 2 j) =
      (word C hC i j).map (subcomplexGraphInclusion (hC hik)) := by
  unfold word
  rw [BoundaryWords.map_comp, subcomplexGraphInclusion_comp]
  rfl

def complex (i : Fin (n + 1)) : Comb.Complex2 where
  V := (subcomplexGraph (C i)).V
  E := (subcomplexGraph (C i)).E
  F := RelCWComplex.cell (C i : Set X) 2
  src := (subcomplexGraph (C i)).src
  tgt := (subcomplexGraph (C i)).tgt
  base j := (word C hC i j).vertex (squareSideMap (0, false) 0)
  att j := (word C hC i j).loopWord
  att_isLoop j := (word C hC i j).loopWord_isPath

theorem word_loop_natural {i k : Fin (n + 1)} (hik : i ≤ k)
    (j : RelCWComplex.cell (C i : Set X) 2) :
    (word C hC k (subcomplexCellInclusion (hC hik) 2 j)).loopWord =
      Comb.mapPath (subcomplexGraphInclusion (hC hik)) (word C hC i j).loopWord := by
  rw [word_natural C hC hik j]
  exact BoundaryWords.loopWord_map _ _

def inclusion {i k : Fin (n + 1)} (hik : i ≤ k) : Comb.Hom (complex C hC i) (complex C hC k) where
  onV := (subcomplexGraphInclusion (hC hik)).onV
  onE := (subcomplexGraphInclusion (hC hik)).onE
  onF := subcomplexCellInclusion (hC hik) 2
  src_onE := (subcomplexGraphInclusion (hC hik)).src_onE
  tgt_onE := (subcomplexGraphInclusion (hC hik)).tgt_onE
  base_onF j := by
    change (word C hC k (subcomplexCellInclusion (hC hik) 2 j)).vertex _ = _
    rw [word_natural C hC hik j]
    rfl
  att_onF j := word_loop_natural C hC hik j

theorem inclusion_injective_V {i k : Fin (n + 1)} (hik : i ≤ k) :
    Function.Injective (inclusion C hC hik).onV :=
  subcomplexGraphInclusion_injective_V (hC hik)

theorem inclusion_injective_E {i k : Fin (n + 1)} (hik : i ≤ k) :
    Function.Injective (inclusion C hC hik).onE :=
  subcomplexGraphInclusion_injective_E (hC hik)

theorem inclusion_injective_F {i k : Fin (n + 1)} (hik : i ≤ k) :
    Function.Injective (inclusion C hC hik).onF :=
  (subcomplexCellInclusion (hC hik) 2).injective

end FiniteChains.ClassicalCW.ChainWords
