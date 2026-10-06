module

public import RequestProject.OriginalChainNecessity
public import RequestProject.OriginalCoverChains
public import RequestProject.OriginalAcyclicChains

@[expose] public section

/-! Proof of Theorem A. The definitions in the statement (`TwoComplex`, `KillsPi2`, `HasChain`,
...) come from `RequestProject.Statement`, whose text is identical to that of `Challenge.lean`;
Comparator checks that they and `TheoremA` agree with `Challenge.lean`. -/

namespace Whitehead

/-- Theorem A, including its finite acyclic clause, without any sufficiency premise. -/
theorem TheoremA (K : TwoComplex) :
    ((∀ n : ℕ, 1 ≤ n → HasChain K n false) ↔
        HasAcyclicRegularCover K) ∧ (FiniteCells K → Acyclic K → ∀ n : ℕ, 1 ≤ n → HasChain K n true) := by
  refine ⟨⟨hasAcyclicRegularCover_of_chains K, ?_⟩, ?_⟩
  · intro h n hn
    exact hasChain_of_acyclicRegularCover K h n hn
  · intro hfinite hacyclic n hn
    exact hasFiniteChain_of_acyclic K hfinite hacyclic n hn

end Whitehead
