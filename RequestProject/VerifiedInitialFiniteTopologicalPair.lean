import RequestProject.VerifiedFiniteCockcroft
import RequestProject.InitialFiniteTopologicalPair

/-! The first actual finite CW extension has been constructed from the initial
Fox pair. Literal labelled presentation embeddings preserve the selected word
positions, yield genuine CW subcomplexes, and preserve the original open cells.
The induced map kills actual topological pi2, and the target is Cockcroft.

`initial_valid_hasChain_one` proves the exact finite one-step HasChain clause
for the canonical finite model of a finite presentation whose exponent-sum
matrix is bijective and which has a chosen generator.

This file is an intermediate integration point. The full theorem, including
the arbitrary CW and finite clauses, is proved by Whitehead.TheoremA in
Solution.lean.
-/
