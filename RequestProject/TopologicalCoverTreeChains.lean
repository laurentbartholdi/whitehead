module

public import RequestProject.TopologicalCoverCellChains
public import RequestProject.RegularCoverFreshCells
public import RequestProject.TreeChainPresentationRealization
public import RequestProject.StrictTriangleTreeGenerator

@[expose] public section

/-! Assemble all sufficiency steps after a specified initial tree-model
comparison. The displayed comparison is the outstanding geometric input;
no covering, matrix, strictness, or spherical-generation premise is hidden.
This is an intermediate theorem, not Whitehead.MainClaim. Pending Lean check. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Comb
open CategoryTheory PresModel SpanningTree
variable (P : Type) [PartialOrder P] [Nonempty P] [(nerve P).HasDimensionLE 2]
  (hP : IsConnected (orderCx P))

theorem hasChain_of_topological_cover_tree_comparison (X : Whitehead.TwoComplex)
    (T₀ : SpanningTree (strictOrderCx P)) (a : NonTree T₀)
    (e₀ : ContinuousMap.HomotopyEquiv
      (ClassicalPresWordDisks (presCanonicalWords (treeRel T₀) a)
        (presCanonicalWords_ne_nil (treeRel T₀) a)) X)
    (h : Whitehead.HasAcyclicRegularCover (orderNerveTwoComplex P hP)) (n : ℕ) :
    Whitehead.HasChain X (n + 1) false := by
  obtain ⟨E, tE, p, hp, hs, hconn, hr, hac⟩ := h
  letI := tE
  letI := hconn
  obtain ⟨hcover, hregular, hconnected, hacyclic, hedge, hface⟩ :=
    TopologicalOrderCover.reconstructed_cover_conclusions p hp hs hr hac
  let proj := TopologicalOrderCover.strictProjection p hp hs
  let action := TopologicalOrderCover.strictDeckAction p hp
  obtain ⟨d, -⟩ := hcover.surjV (Classical.choice (inferInstance : Nonempty P))
  obtain ⟨T, -⟩ := SpanningTree.exists_of_isConnected hconnected d
  let c := regularCoverTopChain T hacyclic proj hcover action hregular hedge hface n
  exact c.hasOriginalChain_of_initial_tree_comparison T₀ X a e₀
    (fun i hi => regularCoverChain_freshLoopOrFace T hacyclic proj n i hi)

end FiniteChains.Comb

namespace FiniteChains.ClassicalCW
open Comb PresModel SpanningTree

/-- Reduction of the original sufficiency direction to one actual
homotopy equivalence for the initial strict order-complex tree model. -/
theorem hasChain_of_original_cover_tree_comparison (K : Whitehead.TwoComplex)
    (T₀ : SpanningTree (strictOrderCx (CanonicalPos K)))
    (e₀ : ContinuousMap.HomotopyEquiv
      (ClassicalPresWordDisks (presCanonicalWords (treeRel T₀) (canonicalTreeGenerator K T₀))
        (presCanonicalWords_ne_nil (treeRel T₀) (canonicalTreeGenerator K T₀)))
      (orderNerveRealization (CanonicalPos K)))
    (h : Whitehead.HasAcyclicRegularCover K) (n : ℕ) :
    Whitehead.HasChain K (n + 1) false :=
  hasChain_of_topological_cover_tree_comparison (CanonicalPos K)
    (presPos_isConnected _ (canonicalWords_ne_nil K)) K T₀ (canonicalTreeGenerator K T₀)
    (e₀.trans (originalCanonicalTwoComplexEquiv K).symm)
    (canonicalTwoComplex_hasCover K h) n

end FiniteChains.ClassicalCW
