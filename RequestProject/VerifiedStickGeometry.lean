module

public import RequestProject.TopologicalSingular.TetrahedronStickShell
public import RequestProject.TopologicalSingular.SingularHornFilling

@[expose] public section

/-!
# Stick coordinates, based triangles, and explicit horn fillers

The recursively defined cube-to-simplex map preserves the oriented face
table. In dimension two it agrees on the whole boundary with the triangle
parametrization used for this project's Hurewicz map, so both give the same
actual based homotopy class. A tetrahedron with constant edges and constant
zeroth face consequently satisfies [face 1] + [face 3] = [face 2] in pi2.

The explicit retraction of every simplex onto any of its horns supplies a
continuous filler for any compatible family of maps on all but one face.
The filler agrees exactly with the prescribed maps, for arbitrary target
topological spaces. The relevant geometric lemmas from the reference
repository have been isolated and ported to the pinned Lean toolchain.

The general four-face relation, Hurewicz injectivity, the CW construction
and descent steps are provided by other modules; the public endpoint is
Whitehead.TheoremA in Solution.lean.
-/
