import RequestProject.TopologicalSingular.NormalizedThreeChains
import RequestProject.TopologicalSingular.BasedTetrahedronDisks
import RequestProject.TopologicalSingular.TetrahedronFaceNullHomotopy

/-!
# Coherent tetrahedra and genuine based homotopies

The normalization of singular triangles extends to tetrahedra with exactly
the prescribed face homotopies. Normalization commutes with the boundary of
every singular 3-chain and has an explicit prism chain homotopy.

The two disks in a tetrahedron, formed by its two complementary pairs of
faces, are homotopic relative to the square boundary. For a tetrahedron with
constant edges this is a homotopy of actual `GenLoop (Fin 2)` representatives,
and hence an equality in Mathlib's genuine `HomotopyGroup (Fin 2)`.
If three faces are constant, the fourth is explicitly nullhomotopic relative
to its whole boundary and gives the identity in that same homotopy group.

This file is an intermediate integration point. The full theorem, including
the arbitrary CW and finite clauses, is proved by Whitehead.TheoremA in
Solution.lean.
-/
