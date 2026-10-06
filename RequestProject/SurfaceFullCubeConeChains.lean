import RequestProject.OrderConeChains
import RequestProject.SurfaceFullCubeFilling

/-! Explicit cone-edge fans for the actual cut-surface inclusion. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] (A : CommRel V)

/-- The explicit positive-corner fan on a finite surface edge chain. -/
noncomputable def surfaceCornerFan :
    ((orderCx (NeSpx A)).E →₀ ℤ) →ₗ[ℤ] ((orderCx (QCube A)).F →₀ ℤ) :=
  coneEdgeChain (surfaceFullCube A) (surfaceFullCube_monotone A)
    (positiveCorner A) (positiveCorner_le_surface A)

/-- An actual surface loop bounds this explicit fan of triangles through the corner. -/
theorem surfaceCornerFan_loop_boundary {σ : NeSpx A}
    {p : List ((orderCx (NeSpx A)).E × Bool)}
    (hp : IsPath (orderCx (NeSpx A)).src (orderCx (NeSpx A)).tgt p σ σ) :
    Comb.bdry2 (orderCx (QCube A)) (surfaceCornerFan A (pathChain p)) =
      pathChain (mapPath (orderCxMap (surfaceFullCube A) (surfaceFullCube_monotone A)) p) :=
  coneEdgeChain_loop_boundary _ _ _ _ hp

end FiniteChains.Davis
