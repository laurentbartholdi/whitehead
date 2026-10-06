module

public import RequestProject.VerifiedChamberPi2
public import RequestProject.OrderEmbeddedTopologicalChains
public import RequestProject.ChamberRelativeCells

@[expose] public section

/-! # Actual cell-preserving embeddings and compatible CW chains

Realizing an order embedding identifies its source with a genuine CW
subcomplex, with a proved bijection preserving every original open cell.
A compatible family of embeddings into a common two-dimensional order model
therefore gives the exact HasChain of Challenge, when its strictness and actual
pi2 conditions have been proved. Finite ambient orders give finite ambient cells.

For the chamber construction the original base is a proper actual subcomplex
when a Coxeter generator is present. The chamber realization has finitely many
cells when both the base and generator type are finite.

This file is an intermediate integration point. The full theorem, including
the arbitrary CW and finite clauses, is proved by Whitehead.TheoremA in
Solution.lean.
-/
