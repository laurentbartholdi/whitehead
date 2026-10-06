module

public import RequestProject.TopologicalCoverTreeChains
public import RequestProject.OrderTriangleTreeComparison

@[expose] public section

/-! The unrestricted sufficiency direction of the original theorem:
an actual connected acyclic regular covering gives strict chains of
arbitrary positive length starting with the original CW cells.
Source assembled; final Lean verification remains outstanding. -/

noncomputable section
open scoped Classical
namespace Whitehead
open FiniteChains FiniteChains.Comb FiniteChains.ClassicalCW FiniteChains.PresModel

theorem hasChain_of_acyclicRegularCover (K : TwoComplex)
    (h : HasAcyclicRegularCover K) (n : ℕ) (hn : 1 ≤ n) : HasChain K n false := by
  let hP := presPos_isConnected (canonicalWords K) (canonicalWords_ne_nil K)
  obtain ⟨T, -⟩ := SpanningTree.exists_of_isConnected
    (strictOrderCx_isConnected hP)
    (Classical.choice (inferInstance : Nonempty (CanonicalPos K)))
  let e₀ := OrderTriangleWords.canonicalTreeDiskRealizationEquiv
    (CanonicalPos K) T (canonicalTreeGenerator K T) hP
  cases n with
  | zero => omega
  | succ n => exact hasChain_of_original_cover_tree_comparison K T e₀ h n

end Whitehead
