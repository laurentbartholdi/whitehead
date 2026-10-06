module

public import RequestProject.VerifiedCoveredSpineHomology
public import RequestProject.GenusOldCoverSpineHomology
public import RequestProject.ChamberQuotientAttachingCycles
public import RequestProject.ChamberQuotientOldCover

@[expose] public section

/-!
Checked integration point for two actual geometric inputs of the relative block
comparison. Pulling back any old-cell cover constructs the corresponding cover
of the truncated block, with an explicit retraction and prism homotopy. This
reflects fillings of actual covered-spine cycles and gives an injective map on
genuine integral singular H2, without assuming a covered chain equivalence.

The quotient Q splits into its old cells and the star of its inserted base.
Every comparable pair lies in one piece. Ambient universal-cover generation
therefore gives old-cell generation by the intersection, with finite correction
chains entirely supported on old cells. The intersection is identified with
the actual attaching simplex poset, and its preimage is proved to cover that
poset. The residual cycles are actual homogeneous chains of that cover.

This file is an intermediate integration point. The full theorem, including
the arbitrary CW and finite clauses, is proved by Whitehead.TheoremA in
Solution.lean.
-/
