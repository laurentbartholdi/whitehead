import RequestProject.ClassicalCWChainPresentation
import RequestProject.ClassicalChartedGraphComparison

/-! Prescribed original graph words are retained at stage zero. The
remaining cells still obtain actual words and homotopies from the graph
approximation theorem. Unverified source. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment PresModel
open Set Topology
open scoped Classical
variable (K : Whitehead.TwoComplex) {n : ℕ}
  (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C)

def seededChoices
    (W : ∀ _j : RelCWComplex.cell (C 0 : Set K) 2,
      BoundaryWords (skeletonAttachingMap (C 0 : Set K) 1))
    (hW : ∀ j, (subcomplexCellBoundary (C 0) j).Homotopic (W j).boundaryMap) : Choices C where
  cellWord i j := if hi : i = 0 then by subst i; exact W j
    else Classical.choose (subcomplexCellBoundary_word_exists (C i) j)
  cellWord_spec i j := by
    split_ifs with hi
    · subst i
      exact hW j
    · exact Classical.choose_spec (subcomplexCellBoundary_word_exists (C i) j)

theorem seededChoices_zero
    (W : ∀ _j : RelCWComplex.cell (C 0 : Set K) 2,
      BoundaryWords (skeletonAttachingMap (C 0 : Set K) 1))
    (hW : ∀ j, (subcomplexCellBoundary (C 0) j).Homotopic (W j).boundaryMap)
    (j : RelCWComplex.cell (C 0 : Set K) 2) :
    Choices.cellWord (self := seededChoices K C W hW) 0 j = W j := by
  rfl

theorem birth_zero (j : RelCWComplex.cell (C 0 : Set K) 2) :
    birth C (topCell C hC 0 j) = 0 :=
  le_antisymm (birth_le C (topCell C hC 0 j) 0 j.property) (Fin.zero_le _)

theorem word_zero [Choices C] (j : RelCWComplex.cell (C 0 : Set K) 2) :
    word C hC 0 j = Choices.cellWord 0 j := by
  have hh (a : Fin (n + 1)) (ha : a ≤ 0) (hj : j.val ∈ (C a).I 2) :
      (Choices.cellWord a ⟨j.val, hj⟩).map (subcomplexGraphInclusion (hC ha)) =
        Choices.cellWord 0 j := by
    have hz : a = 0 := le_antisymm ha (Fin.zero_le _)
    subst a
    have he : subcomplexGraphInclusion (hC ha) = Comb.Hom.id (subcomplexGraph (C 0)) := by
      apply Comb.Hom.ext'
      · rfl
      · rfl
      · funext f
        exact Empty.elim f
    rw [he]
    change (Choices.cellWord 0 j).map (Comb.Hom.id (subcomplexGraph (C 0))) = Choices.cellWord 0 j
    cases Choices.cellWord 0 j
    simp [BoundaryWords.map, Comb.Hom.id, Comb.mapPath]
  exact hh (birth C (topCell C hC 0 j))
    (birth_le C (topCell C hC 0 j) 0 j.property) (birth_mem C (topCell C hC 0 j))

def seededTreeChoice (T : Comb.SpanningTree (subcomplexGraph (C 0))) : TreeChoice K C := ⟨some T⟩

end FiniteChains.ClassicalCW.ChainWords

namespace FiniteChains.ClassicalCW
open ClassicalGraphModel Comb Topology
open scoped Classical
variable (K : Whitehead.TwoComplex) (T : SpanningTree (originalGraph K))

abbrev FixedGen := SpanningTree.NonTree T ⊕ PUnit.{1}
abbrev FixedRel := RelCWComplex.cell (Set.univ : Set K) 2 ⊕ PUnit.{1}

def fixedRelators : FixedRel K → FreeGroup (FixedGen K T)
  | .inl j => FreeGroup.map Sum.inl (SpanningTree.pathWord T (fixedGraphWord K j).loopWord)
  | .inr _ => FreeGroup.of (Sum.inr PUnit.unit)

end FiniteChains.ClassicalCW
