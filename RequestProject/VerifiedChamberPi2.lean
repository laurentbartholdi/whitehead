module

public import RequestProject.ChamberTopologicalFunctor
public import RequestProject.OrderTwoDimensionalH2Injection

@[expose] public section

/-! # Actual pi2 descent for the constructed chamber quotient

For a monotone map from Qpos to a connected order realization, killing actual
topological pi2 is equivalent to killing actual pi2 on the original base.
This uses the already proved finite equivariant cycle decomposition, explicit
three-fillings under deck transformations, genuine Hurewicz, and the actual
universal-cover comparison. Generation is not an extra hypothesis.

The quotient construction acts on monotone base maps and preserves order
embeddings and composition. Its actual realization preserves pi2 vanishing.
The terminal-step implication follows when the restriction to a Cockcroft base
kills combinatorial pi1, via its proved monotone lift.

Separately, an order embedding into a two-dimensional nerve is injective on
actual integral singular H2. Thus a pi2-killing such embedding forces the
source realization to be Cockcroft. Normalization handles the weak nerve's
degenerate simplices and their genuine three-boundaries.

This file is an intermediate integration point. The full theorem, including
the arbitrary CW and finite clauses, is proved by Whitehead.TheoremA in
Solution.lean.
-/
