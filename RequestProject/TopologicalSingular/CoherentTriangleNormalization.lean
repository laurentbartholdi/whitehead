module

public import RequestProject.TopologicalSingular.CoherentEdgeNormalization
public import RequestProject.TopologicalSingular.TriangleBasedNormalization

@[expose] public section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem normalizedEdgeHomotopies_coherent (x : X) (tau : Simplex X 2)
    (i j : Fin 3) (t : I) (z w : Domain 1)
    (h : stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w) :
    normalizedEdgeHomotopy x (face i tau) (t, z) = normalizedEdgeHomotopy x (face j tau) (t, w) := by
  by_cases hij : i = j
  · subst j
    rw [simplex_face_injective i h]
  · obtain ⟨hz, hw⟩ := simplex_face_intersection_boundary i j hij z w h
    rw [normalizedEdgeHomotopy_boundary x _ _ _ hz, normalizedEdgeHomotopy_boundary x _ _ _ hw,
      face_apply, face_apply, h]

theorem normalizedTriangle_exists (x : X) (tau : Simplex X 2) :
    ∃ g : Simplex X 2, ∃ F : tau.Homotopy g,
      ∀ (i : Fin 3) (t : I) (z : Domain 1),
        F (t, stdSimplex.map (SimplexCategory.δ i) z) = normalizedEdgeHomotopy x (face i tau) (t, z) :=
  simplex_face_homotopy_extension tau
    (fun i => (normalizedEdgeHomotopy x (face i tau)).toContinuousMap)
    (normalizedEdgeHomotopies_coherent x tau)
    (fun i z => (normalizedEdgeHomotopy x (face i tau)).apply_zero z)

noncomputable def normalizedTriangle (x : X) (tau : Simplex X 2) : Simplex X 2 :=
  (normalizedTriangle_exists x tau).choose

noncomputable def normalizedTriangleHomotopy (x : X) (tau : Simplex X 2) :
    tau.Homotopy (normalizedTriangle x tau) :=
  (normalizedTriangle_exists x tau).choose_spec.choose

theorem normalizedTriangleHomotopy_face (x : X) (tau : Simplex X 2)
    (i : Fin 3) (t : I) (z : Domain 1) :
    normalizedTriangleHomotopy x tau (t, stdSimplex.map (SimplexCategory.δ i) z) =
      normalizedEdgeHomotopy x (face i tau) (t, z) :=
  (normalizedTriangle_exists x tau).choose_spec.choose_spec i t z

theorem normalizedTriangle_face (x : X) (tau : Simplex X 2) (i : Fin 3) :
    face i (normalizedTriangle x tau) = ContinuousMap.const (Domain 1) x := by
  apply ContinuousMap.ext
  intro z
  have he := normalizedTriangleHomotopy_face x tau i 1 z
  rw [(normalizedTriangleHomotopy x tau).apply_one, (normalizedEdgeHomotopy x (face i tau)).apply_one] at he
  exact he

end FiniteChains.TopologicalSingular
