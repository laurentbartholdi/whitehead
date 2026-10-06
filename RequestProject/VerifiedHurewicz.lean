module

public import RequestProject.TopologicalSingular.Pi2HurewiczHom
public import RequestProject.TopologicalSingular.BasedTriangleHurewicz
public import RequestProject.TopologicalSingular.TriangleBasedNormalization

@[expose] public section

/-! Checked infrastructure for the genuine degree-two Hurewicz map.

`singularHurewicz2Hom` has domain Mathlib's actual `HomotopyGroup (Fin 2)`
and codomain its integral `singularHomologyFunctor` in degree two. Its
well-definedness, naturality and group law are proved. Normalized based
triangles are represented by genuine square maps with an exact chain
identity. Homotopies on simplex boundaries extend over whole simplices,
and triangles with based vertices can be deformed to based triangles in
a simply connected target.

This file is an intermediate integration point. The full theorem, including
the arbitrary CW and finite clauses, is proved by Whitehead.TheoremA in
Solution.lean.
-/
