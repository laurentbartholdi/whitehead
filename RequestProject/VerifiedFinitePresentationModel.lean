module

public import RequestProject.VerifiedEmbeddedChains
public import RequestProject.PresValidPi2

@[expose] public section

/-! # A genuine finite model for finite presentations

The old PresPos uses every natural position for every relator; hence finite
generator and relator types do not imply its finiteness. ValidPresPos keeps
precisely the valid positions, together with the rose and all relator apices.
Its nerve is two-dimensional and connected when all chosen words are nonempty.
Finite presentations give Whitehead.FiniteCells for validPresTwoComplex.

A monotone retraction fixes the retained subposet. Its realization has a proved
jointly continuous deformation, stationary on that subcomplex. Consequently
there is an actual homotopy equivalence, an isomorphism of genuine singular
homology in every degree, and an isomorphism of Mathlib's genuine pi2 induced
by the actual inclusion, not an assumed comparison map.

This file is an intermediate integration point. The full theorem, including
the arbitrary CW and finite clauses, is proved by Whitehead.TheoremA in
Solution.lean.
-/
