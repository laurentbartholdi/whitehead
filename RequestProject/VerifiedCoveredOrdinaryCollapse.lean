module

public import RequestProject.VerifiedStrictAcyclicityAndSpineFamilies
public import RequestProject.GenusOrdinaryPairCoverHomology

@[expose] public section

/-!
Checked integration point for genuine homology preservation under ordinary
recorded pairs of the chosen genus-block collapse, in arbitrary poset covers.

Comparable maps are lifted in a fixed sheet. Explicit coordinate contractions
fill one- and two-cycles of covered ordinary punctured cube boundaries. Chain
gluing gives both generation and reflection of actual fillings under deletion
of a maximal cell. Finite chain supports extend these two conclusions to an
arbitrary family of maximal cells, without a finite-cover assumption.

All lifts of a recorded free face can be removed by a genuine lifted retraction;
this works for both ordinary and cut faces. For ordinary pairs the remaining
top-cell step is also proved, giving both H2 comparisons between the actual
successive collapse stages, with no relative vanishing premise.

This file is an intermediate integration point. The full theorem, including
the arbitrary CW and finite clauses, is proved by Whitehead.TheoremA in
Solution.lean.
-/
