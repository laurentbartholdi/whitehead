import RequestProject.VerifiedPresentationPi2Naturality
import RequestProject.PresChainRealization
import RequestProject.AsphericalFiniteTopologicalChains

/-! Successive order embeddings now construct their compatible embeddings
in the last stage, yielding the exact CW-subcomplex chain of Challenge.
Properness and original open-cell preservation are proved, and finiteness
of the last order gives actual finite ambient cells.

For labelled presentations, canonical nonempty words are chosen compatibly
along the whole chain. The existing algebraic universal-cover cycle
condition supplies actual topological pi2 vanishing at every step.
PresChainFS.hasTopologicalChain and PresChain.hasFiniteTopologicalChain
apply this directly to existing algebraic chains, starting at their true
zeroth stage. Their external core embeddings are not treated as equalities.

Cancelling generator/relator pairs then construct actual finite CW chains
of every length for the canonical model of a finite aspherical presentation
with a chosen generator. No chain-existence hypothesis remains in that
aspherical case.

This file is an intermediate integration point. The full theorem, including
the arbitrary CW and finite clauses, is proved by Whitehead.TheoremA in
Solution.lean.
-/
