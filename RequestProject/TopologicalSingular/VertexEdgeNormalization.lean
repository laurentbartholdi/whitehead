module

public import RequestProject.TopologicalSingular.SimplexBoundaryGluing

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]

noncomputable def vertexNormalizationHomotopy (x : X) (tau : Simplex X 0) :
    tau.Homotopy (ContinuousMap.const (Domain 0) x) where
  toFun w := PathConnectedSpace.somePath (tau (stdSimplex.vertex 0)) x w.1
  continuous_toFun := (PathConnectedSpace.somePath _ _).continuous.comp continuous_fst
  map_zero_left z := by
    rw [Path.source]
    apply congrArg tau
    apply Subtype.ext
    funext i
    have hz := z.property.2
    simpa [stdSimplex.vertex, show i = 0 by omega] using hz.symm
  map_one_left _ := Path.target _

theorem vertexNormalizationHomotopy_apply (x : X) (tau : Simplex X 0) (t : I) (z : Domain 0) :
    vertexNormalizationHomotopy x tau (t, z) = PathConnectedSpace.somePath (tau z) x t := by
  have hz : stdSimplex.vertex 0 = z :=
    by
      apply Subtype.ext
      funext i
      have hz := z.property.2
      simpa [stdSimplex.vertex, show i = 0 by omega] using hz.symm
  change PathConnectedSpace.somePath (tau (stdSimplex.vertex 0)) x t = _
  rw [hz]

/-- Endpoint motion for every edge is chosen from the original endpoint
itself, so different edges incident at that endpoint move it identically. -/
theorem edgeVertexNormalization_exists (x : X) (tau : Simplex X 1) :
    ∃ g : Simplex X 1, ∃ F : tau.Homotopy g,
      ∀ (t : I) (z : Domain 1), z ∈ simplexBoundary 1 →
        F (t, z) = PathConnectedSpace.somePath (tau z) x t := by
  obtain ⟨g, F, hF⟩ := simplex_face_homotopy_extension tau
    (fun i => (vertexNormalizationHomotopy x (face i tau)).toContinuousMap)
    (by
      intro i j t z w h
      change vertexNormalizationHomotopy x (face i tau) (t, z) =
        vertexNormalizationHomotopy x (face j tau) (t, w)
      simp only [vertexNormalizationHomotopy_apply, face_apply]
      exact congrArg (fun a : X => PathConnectedSpace.somePath a x t) (congrArg tau h))
    (fun i z => (vertexNormalizationHomotopy x (face i tau)).apply_zero z)
  refine ⟨g, F, ?_⟩
  intro t z hz
  obtain ⟨i, hi⟩ := hz
  obtain ⟨w, hw⟩ := domain_zero_coordinate_face z i hi
  rw [← hw, hF]
  exact vertexNormalizationHomotopy_apply x (face i tau) t w

noncomputable def edgeVertexNormalized (x : X) (tau : Simplex X 1) : Simplex X 1 :=
  (edgeVertexNormalization_exists x tau).choose

noncomputable def edgeVertexHomotopy (x : X) (tau : Simplex X 1) :
    tau.Homotopy (edgeVertexNormalized x tau) :=
  (edgeVertexNormalization_exists x tau).choose_spec.choose

theorem edgeVertexHomotopy_boundary (x : X) (tau : Simplex X 1) (t : I)
    (z : Domain 1) (hz : z ∈ simplexBoundary 1) :
    edgeVertexHomotopy x tau (t, z) = PathConnectedSpace.somePath (tau z) x t :=
  (edgeVertexNormalization_exists x tau).choose_spec.choose_spec t z hz

theorem simplexOne_vertex_mem_boundary (i : Fin 2) :
    stdSimplex.vertex i ∈ simplexBoundary 1 := by
  fin_cases i
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

theorem edgeVertexNormalized_vertex (x : X) (tau : Simplex X 1) (i : Fin 2) :
    edgeVertexNormalized x tau (stdSimplex.vertex i) = x := by
  have he := edgeVertexHomotopy_boundary x tau 1 (stdSimplex.vertex i) (simplexOne_vertex_mem_boundary i)
  rw [(edgeVertexHomotopy x tau).apply_one, Path.target] at he
  exact he

end FiniteChains.TopologicalSingular
