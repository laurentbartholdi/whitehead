module

public import RequestProject.TopologicalSingular.BasedTriangleHurewicz
public import RequestProject.TopologicalSingular.SimplexLinearHomotopy
public import RequestProject.TopologicalSingular.SimplexPrismRetraction

@[expose] public section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- Relative homotopies of based triangles give homotopies of the genuine
based squares used to define their classes in pi2. -/
theorem basedTriangleSquare_homotopic (tau eta : Simplex X 2)
    (htau : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x)
    (heta : ∀ i : Fin 3, face i eta = ContinuousMap.const (Domain 1) x)
    (H : ContinuousMap.HomotopyRel tau eta (simplexBoundary 2)) :
    GenLoop.Homotopic (basedTriangleSquare tau htau) (basedTriangleSquare eta heta) := by
  refine ⟨{
    toFun := fun w => H (w.1, squareToTriangle w.2)
    continuous_toFun := H.continuous.comp (continuous_fst.prodMk
      (squareToTriangle.continuous.comp continuous_snd))
    map_zero_left := fun z => H.apply_zero (squareToTriangle z)
    map_one_left := fun z => H.apply_one (squareToTriangle z)
    prop' := ?_ }⟩
  intro t z hz
  exact H.eq_fst t (squareToTriangle_boundary z hz)

theorem basedTriangleSquare_const
    (h : ∀ i : Fin 3,
      face i (ContinuousMap.const (Domain 2) x) = ContinuousMap.const (Domain 1) x) :
    basedTriangleSquare (ContinuousMap.const (Domain 2) x) h = GenLoop.const := by
  apply GenLoop.ext
  intro z
  rfl

theorem basedTriangleSquare_nullhomotopic (tau : Simplex X 2)
    (htau : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x)
    (H : ContinuousMap.HomotopyRel tau (ContinuousMap.const (Domain 2) x) (simplexBoundary 2)) :
    GenLoop.Homotopic (basedTriangleSquare tau htau) GenLoop.const := by
  have hconst (i : Fin 3) :
      face i (ContinuousMap.const (Domain 2) x) = ContinuousMap.const (Domain 1) x := rfl
  have he := basedTriangleSquare_homotopic tau _ htau hconst H
  rwa [basedTriangleSquare_const] at he

end FiniteChains.TopologicalSingular
