import RequestProject.TopologicalSingular.HurewiczIsomorphismConsequences
import RequestProject.OrderRealizationHurewicz

/-! # Genuine degree-two Hurewicz isomorphism

For any simply connected topological space in Type 0, the canonical map
`singularHurewicz2` from Mathlib's actual `HomotopyGroup (Fin 2)` to its integral
`singularHomologyFunctor` is bijective. Both group and integer-linear
equivalences are supplied, with that canonical natural map as forward map.

Injectivity uses the four-face relation in actual pi2, constructed from
continuous singular horn fillings, and a stationary coherent normalization.
Every actual based square factors through a pointed triangle by the quotient
map given by stick coordinates. The normalized-triangle sum kills every
singular 3-boundary and fixes the class of a pointed triangle exactly.

The comparison is applied to order-nerve realizations and their constructed
universal covers. Earlier integration files document earlier checkpoints;
the injectivity obligation mentioned there is discharged by these imports.

This file is an intermediate integration point. The full theorem, including
the arbitrary CW and finite clauses, is proved by Whitehead.TheoremA in
Solution.lean.
-/
