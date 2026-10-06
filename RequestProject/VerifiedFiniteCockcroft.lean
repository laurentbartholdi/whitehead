import RequestProject.VerifiedFinitePresentationModel
import RequestProject.PresFiniteTopologicalCockcroft

/-! The actual finite presentation model inherits the genuine topological
Cockcroft property from the already checked Fox calculation. The comparison
uses explicit universal-cover cycle fillings, the actual Hurewicz theorem and
the stationary deformation onto the valid-position subcomplex.

This file is an intermediate integration point. The full theorem, including
the arbitrary CW and finite clauses, is proved by Whitehead.TheoremA in
Solution.lean.
-/
