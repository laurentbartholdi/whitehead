module

public import RequestProject.VerifiedRelativeBoundaryFillings
public import RequestProject.GenusSpineSubstitutedBoundary
public import RequestProject.TreeCoverRelativeBoundary

@[expose] public section

/-!
The internal Fox boundary of the actual substituted finite spine has been
identified with its marked relative boundary, over the actual substituted group
ring. The homomorphism sending block coefficients there is explicitly constructed.
The exact relative boundary comparison through a spanning-tree collapse is proved
for genuine regular covers, without finiteness restrictions on their cell sets.

This file is an intermediate integration point. The full theorem, including
the arbitrary CW and finite clauses, is proved by Whitehead.TheoremA in
Solution.lean.
-/
