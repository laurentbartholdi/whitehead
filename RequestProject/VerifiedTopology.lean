module

public import RequestProject.GenusCappedSingularHomologyPushdown
public import RequestProject.DavisRealizationAcyclic
public import RequestProject.OrderUniversalRealizationHomologyOne
public import RequestProject.OrderUniversalRealizationPi2

@[expose] public section

/-!
This file is an intermediate integration point. The full theorem, including
the arbitrary CW and finite clauses, is proved by Whitehead.TheoremA in
Solution.lean.
-/

#print axioms FiniteChains.Comb.orderNerveSingularH2Comparison_epi
#print axioms FiniteChains.Davis.Genus.cappedSpineQuotient_singular_homology_pushdown_zero
#print axioms FiniteChains.Comb.orderSmallHomotopy_boundary
#print axioms FiniteChains.Comb.orderNerveRealization_acyclic_of_nerve
#print axioms FiniteChains.Davis.davisRealization_acyclic
#print axioms FiniteChains.Comb.uOrderRealization_simplyConnected
#print axioms FiniteChains.Comb.uOrderRealizationPi2Equiv
