module

public import RequestProject.VerifiedInitialFiniteTopologicalPair
public import RequestProject.CanonicalPresentationTopologicalPair

@[expose] public section

/-! The actual lift of a labelled presentation inclusion to universal covers
commutes with lifted-relator coordinates and the induced presentation-group
homomorphism. No injectivity of that group homomorphism is assumed.

For these genuinely two-dimensional presentation realizations, the actual
topological pi2 map vanishes exactly when all Fox-kernel cycles vanish under
the induced coefficient map. This is also equivalent to the existing
algebraic universal-cover criterion and to Comb.ZeroPi2 for the labelled
presentation inclusion, including with infinite sets of cells.

The implication to actual pi2 vanishing is transferred through the proved
retractions to the valid-position models. A proper algebraic presentation
extension therefore produces the exact one-step Whitehead.HasChain for its
canonical model, preserving original open cells. Finite target generator
and relator sets imply actual finite ambient CW cells.

This file is an intermediate integration point. The full theorem, including
the arbitrary CW and finite clauses, is proved by Whitehead.TheoremA in
Solution.lean.
-/
