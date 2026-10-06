import RequestProject.TopologicalSingular.SimplexPrismRetraction
import RequestProject.TopologicalSingular.SingularChainH1

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X]

theorem simplexOne_boundary_endpoints (z : Domain 1) (hz : z ∈ simplexBoundary 1) :
    stdSimplexHomeomorphUnitInterval z = 0 ∨ stdSimplexHomeomorphUnitInterval z = 1 := by
  have hs : z.val 0 + z.val 1 = 1 := (Fin.sum_univ_two z.val).symm.trans z.property.2
  obtain ⟨i, hi⟩ := hz
  fin_cases i
  · right
    apply Subtype.ext
    change z.val 1 = 1
    change z.val 0 = 0 at hi
    linarith
  · left
    apply Subtype.ext
    exact hi

/-- In a simply connected space, a singular edge whose two vertices are at
the basepoint contracts to the constant edge while fixing both vertices. -/
theorem singularEdge_nullhomotopic [SimplyConnectedSpace X] (x : X) (tau : Simplex X 1)
    (h0 : tau (stdSimplex.vertex 0) = x) (h1 : tau (stdSimplex.vertex 1) = x) :
    Nonempty (ContinuousMap.HomotopyRel tau (ContinuousMap.const (Domain 1) x) (simplexBoundary 1)) := by
  let p : Path x x := {
    toFun := fun t => tau (stdSimplexHomeomorphUnitInterval.symm t)
    continuous_toFun := tau.continuous.comp stdSimplexHomeomorphUnitInterval.symm.continuous
    source' := (congrArg tau (stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr
      stdSimplexHomeomorphUnitInterval_zero.symm)).trans h0
    target' := (congrArg tau (stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr
      stdSimplexHomeomorphUnitInterval_one.symm)).trans h1 }
  obtain ⟨G⟩ := SimplyConnectedSpace.paths_homotopic p (Path.refl x)
  refine ⟨{
    toFun := fun w => G (w.1, stdSimplexHomeomorphUnitInterval w.2)
    continuous_toFun := G.continuous.comp (continuous_fst.prodMk
      (stdSimplexHomeomorphUnitInterval.continuous.comp continuous_snd))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro z
    rw [G.apply_zero]
    change tau (stdSimplexHomeomorphUnitInterval.symm (stdSimplexHomeomorphUnitInterval z)) = tau z
    rw [stdSimplexHomeomorphUnitInterval.symm_apply_apply]
  · intro z
    exact G.apply_one _
  · intro t z hz
    change G (t, stdSimplexHomeomorphUnitInterval z) = tau z
    rcases simplexOne_boundary_endpoints z hz with he | he
    · have hv : z = stdSimplex.vertex 0 := stdSimplexHomeomorphUnitInterval.injective
        (he.trans stdSimplexHomeomorphUnitInterval_zero.symm)
      rw [he, G.source, hv, h0]
    · have hv : z = stdSimplex.vertex 1 := stdSimplexHomeomorphUnitInterval.injective
        (he.trans stdSimplexHomeomorphUnitInterval_one.symm)
      rw [he, G.target, hv, h1]

end FiniteChains.TopologicalSingular
