import RequestProject.TopologicalOrderCoverAcyclic
import RequestProject.RegularCoverAcyclicChains

/-! A genuine topological acyclic regular cover of an order realization
supplies the actual strict cellular chains used in sufficiency. This
consumes the original topological predicates and reconstructs the deck
action, including its edge and face compatibility. Pending final Lean
verification. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Comb
open CategoryTheory
variable (P : Type) [PartialOrder P] [Nonempty P] [(nerve P).HasDimensionLE 2]
  (hP : IsConnected (orderCx P))

theorem strictCellChains_of_topological_cover
    (h : Whitehead.HasAcyclicRegularCover (orderNerveTwoComplex P hP)) (n : ℕ) :
    ∃ c : TopChainFS (strictOrderCx P) (n + 1), c.X 0 = strictOrderCx P ∧
      ∀ i, i < n + 1 → (¬ Function.Surjective (c.inc i).onE) ∨
        (¬ Function.Surjective (c.inc i).onF) := by
  obtain ⟨E, tE, p, hp, hs, hconn, hr, hac⟩ := h
  letI := tE
  letI := hconn
  obtain ⟨hcover, hregular, hconnected, hacyclic, hedge, hface⟩ :=
    TopologicalOrderCover.reconstructed_cover_conclusions p hp hs hr hac
  let proj := TopologicalOrderCover.strictProjection p hp hs
  let action := TopologicalOrderCover.strictDeckAction p hp
  obtain ⟨d, -⟩ := hcover.surjV (Classical.choice (inferInstance : Nonempty P))
  obtain ⟨T, -⟩ := SpanningTree.exists_of_isConnected hconnected d
  refine ⟨regularCoverTopChain T hacyclic proj hcover action hregular hedge hface n, rfl, ?_⟩
  intro i hi
  exact regularCoverChain_proper T hacyclic proj n i hi

end FiniteChains.Comb
