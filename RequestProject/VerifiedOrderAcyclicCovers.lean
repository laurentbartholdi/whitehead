module

public import RequestProject.VerifiedPresentationTopologicalChains
public import RequestProject.PresAsphericalAcyclicCover
public import RequestProject.OrderAcyclicRegularCover

@[expose] public section

/-!
Checked integration point for genuine singular acyclicity of order realizations
and genuine regular acyclic topological covers.

The normalization projector proves vanishing above the actual nerve dimension.
Strict cellular acyclicity therefore implies singular acyclicity in dimension two.
Connected regular order covers with acyclic strict cellular complexes satisfy the
exact `Whitehead.HasAcyclicRegularCover` predicate, without a universal-cover premise.
For the constructed universal cover, acyclicity is equivalent to zero actual pi2.
Finite Fox-aspherical canonical presentation models now have both actual finite
chains of every length and an actual connected regular acyclic cover.

This file is an intermediate integration point. The full theorem, including
the arbitrary CW and finite clauses, is proved by Whitehead.TheoremA in
Solution.lean.
-/
