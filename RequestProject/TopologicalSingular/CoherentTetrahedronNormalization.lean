module

public import RequestProject.TopologicalSingular.CoherentSimplexExtension
public import RequestProject.TopologicalSingular.CoherentTriangleNormalization

@[expose] public section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem normalizedTetrahedron_exists (x : X) (tau : Simplex X 3) :
    ∃ g : Simplex X 3, ∃ F : tau.Homotopy g,
      ∀ (i : Fin 4) (t : I) (z : Domain 2),
        F (t, stdSimplex.map (SimplexCategory.δ i) z) =
          normalizedTriangleHomotopy x (face i tau) (t, z) :=
  compatibleSimplexHomotopyExtension_exists
    (fun _ => ContinuousMap.const (Domain 1) x) (normalizedTriangle x)
    (normalizedEdgeHomotopy x) (normalizedTriangleHomotopy x)
    (normalizedTriangleHomotopy_face x) tau

noncomputable def normalizedTetrahedron (x : X) (tau : Simplex X 3) : Simplex X 3 :=
  (normalizedTetrahedron_exists x tau).choose

noncomputable def normalizedTetrahedronHomotopy (x : X) (tau : Simplex X 3) :
    tau.Homotopy (normalizedTetrahedron x tau) :=
  (normalizedTetrahedron_exists x tau).choose_spec.choose

theorem normalizedTetrahedronHomotopy_face (x : X) (tau : Simplex X 3)
    (i : Fin 4) (t : I) (z : Domain 2) :
    normalizedTetrahedronHomotopy x tau (t, stdSimplex.map (SimplexCategory.δ i) z) =
      normalizedTriangleHomotopy x (face i tau) (t, z) :=
  (normalizedTetrahedron_exists x tau).choose_spec.choose_spec i t z

theorem normalizedTetrahedron_face (x : X) (tau : Simplex X 3) (i : Fin 4) :
    face i (normalizedTetrahedron x tau) = normalizedTriangle x (face i tau) := by
  apply ContinuousMap.ext
  intro z
  have he := normalizedTetrahedronHomotopy_face x tau i 1 z
  rw [(normalizedTetrahedronHomotopy x tau).apply_one,
    (normalizedTriangleHomotopy x (face i tau)).apply_one] at he
  exact he

theorem normalizedTetrahedron_edge (x : X) (tau : Simplex X 3)
    (i : Fin 4) (j : Fin 3) :
    face j (face i (normalizedTetrahedron x tau)) = ContinuousMap.const (Domain 1) x := by
  rw [normalizedTetrahedron_face, normalizedTriangle_face]

end FiniteChains.TopologicalSingular
