import RequestProject.VerifiedOrderAcyclicCovers
import RequestProject.OrderStrictAcyclicityComparison
import RequestProject.GenusMarkedSpineFamily

/-!
Checked integration point for the converse cellular acyclicity comparison and
simultaneous replacement by the actual finite two-dimensional marked spines.

For every nonempty connected two-dimensional order realization, genuine integral
singular acyclicity is equivalent to acyclicity of its strict cellular complex.
The converse uses actual singular H1 and H2, and connectedness supplies H0.

The genuine finite-spine replacement preserves the original presented group
injectively for arbitrary families, including infinite families and varying genera.
Each replaced relation follows from its own block, and finite families add only
finitely many internal generators and relators.

This module assembles acyclicity and group injection. The relative B2 proof,
T/Q construction, and arbitrary CW transfer are assembled downstream by
Solution.lean, whose public endpoint is Whitehead.TheoremA.
-/
