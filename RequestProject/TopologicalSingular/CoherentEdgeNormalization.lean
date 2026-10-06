import RequestProject.TopologicalSingular.VertexEdgeNormalization
import RequestProject.TopologicalSingular.SingularEdgeNullHomotopy

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

noncomputable def edgeVertexNullHomotopy (x : X) (tau : Simplex X 1) :
    ContinuousMap.HomotopyRel (edgeVertexNormalized x tau)
      (ContinuousMap.const (Domain 1) x) (simplexBoundary 1) :=
  Classical.choice (singularEdge_nullhomotopic x (edgeVertexNormalized x tau)
    (edgeVertexNormalized_vertex x tau 0) (edgeVertexNormalized_vertex x tau 1))

noncomputable def normalizedEdgeHomotopy (x : X) (tau : Simplex X 1) :
    tau.Homotopy (ContinuousMap.const (Domain 1) x) :=
  (edgeVertexHomotopy x tau).trans (edgeVertexNullHomotopy x tau).toHomotopy

noncomputable def normalizationVertexPath (x a : X) : Path a x :=
  (PathConnectedSpace.somePath a x).trans (Path.refl x)

/-- Endpoint motion depends only on the original point, for all singular
edges simultaneously; this is the coherence needed for triangle boundaries. -/
theorem normalizedEdgeHomotopy_boundary (x : X) (tau : Simplex X 1) (t : I)
    (z : Domain 1) (hz : z ∈ simplexBoundary 1) :
    normalizedEdgeHomotopy x tau (t, z) = normalizationVertexPath x (tau z) t := by
  rw [normalizedEdgeHomotopy, ContinuousMap.Homotopy.trans_apply,
    normalizationVertexPath, Path.trans_apply]
  split_ifs
  · exact edgeVertexHomotopy_boundary x tau _ z hz
  · exact (edgeVertexNullHomotopy x tau).eq_snd _ hz

end FiniteChains.TopologicalSingular
