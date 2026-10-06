import RequestProject.VerifiedCoveredOrdinaryCollapse
import RequestProject.GenusCoveredSpineCycleFaithfulness

/-!
Checked integration point for the full chosen genus-block collapse in arbitrary
poset covers. The actual seven-cell path contracts by three comparable maps;
gluing the two coordinate pieces proves augmented acyclicity of the punctured
three-cube. The explicit cut-boundary retraction transfers those fillings to
the lower link of each lifted top cell paired with a cut facet.

Both ordinary and cut pairs now preserve H2, simultaneously in every sheet.
Induction along the actual chosen list proves generation by the surviving
spine and reflection of boundaries. Its strict three-flags are empty in any
cover, so a strict two-chain on the covered spine bounding in the whole block
is zero, with all chain encoding and normalization steps verified.

The marked relative comparison, relative T/Q construction, and original CW
transfer are assembled downstream by Solution.lean. This integration point
records the covering-chain comparison used in that proof.
-/
