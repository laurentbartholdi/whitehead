import RequestProject.TopologicalSingular.HurewiczSurjectivityConsequences

/-! Surjectivity checkpoint for the genuine degree-two Hurewicz homomorphism.

`singularHurewicz2Hom_surjective` proves that the actual HomotopyGroup (Fin 2)
surjects onto integral singular H2 in a simply connected space. The proof
normalizes every singular edge and triangle with compatible boundary data,
uses an explicit prism identity for the resulting families, and represents
each normalized triangle by an actual square.

`singularTwoCycle_square_representative` provides the stronger statement
at the chain level: a based square's cycle differs from any prescribed
singular 2-cycle by the boundary of a singular 3-chain.

This file is an intermediate integration point. The full theorem, including
the arbitrary CW and finite clauses, is proved by Whitehead.TheoremA in
Solution.lean.
-/
