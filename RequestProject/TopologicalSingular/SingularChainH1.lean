module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.SingularPathComposition
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

/-! # Exactness in degree one for simply connected spaces

Every singular one-cycle bounds. The proof uses explicit triangles for
concatenation and the two-triangle prism of an actual path homotopy.
No Hurewicz theorem or exactness assumption is used.
-/


namespace FiniteChains.TopologicalSingular

open Set Topology

universe u
variable {X : Type u} [TopologicalSpace X]

def simplexPath (σ : Simplex X 1) : Path (σ (stdSimplex.vertex 0)) (σ (stdSimplex.vertex 1)) where
  toFun t := σ (stdSimplexHomeomorphUnitInterval.symm t)
  continuous_toFun := σ.continuous.comp stdSimplexHomeomorphUnitInterval.symm.continuous
  source' := congrArg σ (stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr
    stdSimplexHomeomorphUnitInterval_zero.symm)
  target' := congrArg σ (stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr
    stdSimplexHomeomorphUnitInterval_one.symm)

theorem pathSimplex_simplexPath (σ : Simplex X 1) : pathSimplex (simplexPath σ) = σ := by
  apply ContinuousMap.ext
  intro z
  exact congrArg σ (stdSimplexHomeomorphUnitInterval.symm_apply_apply z)

theorem path_difference_cone_mem_range [SimplyConnectedSpace X] (root : X)
    {a b : X} (p : Path a b) (r : ℤ) :
    Finsupp.single (pathSimplex p) r -
      pathCone root (boundary 0 (Finsupp.single (pathSimplex p) r)) ∈ LinearMap.range (boundary 1) := by
  let pa := PathConnectedSpace.somePath root a
  let pb := PathConnectedSpace.somePath root b
  have ht := path_trans_relation_mem_range pa p r
  have hh := pathHomotopic_difference_mem_range
    (SimplyConnectedSpace.paths_homotopic (pa.trans p) pb) r
  have hm := (LinearMap.range (boundary (X := X) 1)).sub_mem ht hh
  convert hm using 1
  rw [boundary_pathSimplex, map_sub, pathCone_single, pathCone_single]
  change Finsupp.single (pathSimplex p) r -
    (Finsupp.single (pathSimplex pb) r - Finsupp.single (pathSimplex pa) r) = _
  abel

theorem difference_cone_mem_range [SimplyConnectedSpace X] (root : X) (c : Chain X 1) :
    c - pathCone root (boundary 0 c) ∈ LinearMap.range (boundary 1) := by
  let B : Submodule ℤ (Chain X 1) := LinearMap.range (boundary 1)
  have he : B.mkQ = B.mkQ.comp ((pathCone root).comp (boundary 0)) := by
    apply Finsupp.lhom_ext
    intro σ r
    have hm := path_difference_cone_mem_range root (simplexPath σ) r
    rw [pathSimplex_simplexPath] at hm
    have hz : B.mkQ (Finsupp.single σ r - pathCone root (boundary 0 (Finsupp.single σ r))) = 0 :=
      (Submodule.Quotient.mk_eq_zero B).mpr hm
    rw [map_sub, sub_eq_zero] at hz
    exact hz
  apply (Submodule.Quotient.mk_eq_zero B).mp
  change B.mkQ (c - pathCone root (boundary 0 c)) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (DFunLike.congr_fun he c)

theorem ker_boundary_zero_eq_range_one [SimplyConnectedSpace X] :
    LinearMap.ker (boundary (X := X) 0) = LinearMap.range (boundary 1) := by
  apply le_antisymm
  · intro c hc
    have hm := difference_cone_mem_range (Classical.arbitrary X) c
    simpa only [show boundary 0 c = 0 from hc, map_zero, sub_zero] using hm
  · rintro c ⟨b, rfl⟩
    exact boundary_boundary 0 b

theorem oneCycle_bounds [SimplyConnectedSpace X] (c : Chain X 1) (hc : boundary 0 c = 0) :
    ∃ b : Chain X 2, boundary 1 b = c := by
  have hm : c ∈ LinearMap.ker (boundary (X := X) 0) := hc
  rw [ker_boundary_zero_eq_range_one] at hm
  exact hm

end FiniteChains.TopologicalSingular
