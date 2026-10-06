module

public import RequestProject.TopologicalSingular.StationaryEdgeNormalization
public import RequestProject.TopologicalSingular.CoherentSimplexExtension

@[expose] public section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem stationaryEdgeHomotopies_coherent (x : X) (tau : Simplex X 2)
    (i j : Fin 3) (t : I) (z w : Domain 1)
    (h : stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w) :
    stationaryEdgeHomotopy x (face i tau) (t, z) =
      stationaryEdgeHomotopy x (face j tau) (t, w) := by
  by_cases hij : i = j
  · subst j
    rw [simplex_face_injective i h]
  · obtain ⟨hz, hw⟩ := simplex_face_intersection_boundary i j hij z w h
    rw [stationaryEdgeHomotopy_boundary x _ _ _ hz,
      stationaryEdgeHomotopy_boundary x _ _ _ hw, face_apply, face_apply, h]

/-- Normalize coherently, choosing the identity homotopy whenever the input
triangle already has constant edges. -/
theorem stationaryTriangle_exists (x : X) (tau : Simplex X 2) :
    ∃ g : Simplex X 2, ∃ F : tau.Homotopy g,
      (∀ (i : Fin 3) (t : I) (z : Domain 1),
        F (t, stdSimplex.map (SimplexCategory.δ i) z) =
          stationaryEdgeHomotopy x (face i tau) (t, z)) ∧
      ((∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x) → g = tau) := by
  classical
  by_cases htau : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x
  · refine ⟨tau, ContinuousMap.Homotopy.refl tau, ?_, fun _ => rfl⟩
    intro i t z
    change tau (stdSimplex.map (SimplexCategory.δ i) z) =
      stationaryEdgeHomotopy x (face i tau) (t, z)
    rw [htau i, stationaryEdgeHomotopy_constant]
    exact congrArg (fun f : Simplex X 1 => f z) (htau i)
  · obtain ⟨g, F, hF⟩ := simplex_face_homotopy_extension tau
      (fun i => (stationaryEdgeHomotopy x (face i tau)).toContinuousMap)
      (stationaryEdgeHomotopies_coherent x tau)
      (fun i z => (stationaryEdgeHomotopy x (face i tau)).apply_zero z)
    exact ⟨g, F, hF, fun h => (htau h).elim⟩

noncomputable def stationaryTriangle (x : X) (tau : Simplex X 2) : Simplex X 2 :=
  (stationaryTriangle_exists x tau).choose

noncomputable def stationaryTriangleHomotopy (x : X) (tau : Simplex X 2) :
    tau.Homotopy (stationaryTriangle x tau) :=
  (stationaryTriangle_exists x tau).choose_spec.choose

theorem stationaryTriangleHomotopy_face (x : X) (tau : Simplex X 2)
    (i : Fin 3) (t : I) (z : Domain 1) :
    stationaryTriangleHomotopy x tau (t, stdSimplex.map (SimplexCategory.δ i) z) =
      stationaryEdgeHomotopy x (face i tau) (t, z) :=
  (stationaryTriangle_exists x tau).choose_spec.choose_spec.1 i t z

theorem stationaryTriangle_face (x : X) (tau : Simplex X 2) (i : Fin 3) :
    face i (stationaryTriangle x tau) = ContinuousMap.const (Domain 1) x := by
  apply ContinuousMap.ext
  intro z
  have h := stationaryTriangleHomotopy_face x tau i 1 z
  rw [(stationaryTriangleHomotopy x tau).apply_one,
    (stationaryEdgeHomotopy x (face i tau)).apply_one] at h
  exact h

theorem stationaryTriangle_eq_of_based (x : X) (tau : Simplex X 2)
    (h : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x) :
    stationaryTriangle x tau = tau :=
  (stationaryTriangle_exists x tau).choose_spec.choose_spec.2 h

/-- The stationary normalization remains coherent on all four faces of every
singular tetrahedron, by the relative homotopy extension property. -/
theorem stationaryTetrahedron_exists (x : X) (tau : Simplex X 3) :
    ∃ T : Simplex X 3, ∀ i : Fin 4, face i T = stationaryTriangle x (face i tau) := by
  obtain ⟨T, F, hF⟩ := compatibleSimplexHomotopyExtension_exists
    (fun _ => ContinuousMap.const (Domain 1) x) (stationaryTriangle x)
    (stationaryEdgeHomotopy x) (stationaryTriangleHomotopy x)
    (stationaryTriangleHomotopy_face x) tau
  refine ⟨T, ?_⟩
  intro i
  apply ContinuousMap.ext
  intro z
  have h := hF i 1 z
  rw [F.apply_one, (stationaryTriangleHomotopy x (face i tau)).apply_one] at h
  exact h

end FiniteChains.TopologicalSingular
