module

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
Adapted from Vilin97/homotopy-groups-lean, commit
c66523531ff172d7f41913d94e56921e790a1b47; isolated geometry for Lean 4.28.0.
-/
public import RequestProject.TopologicalSingular.StickSimplex

@[expose] public section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
variable {j : ℕ}

theorem continuous_faceMap (i : Fin (j + 2)) : Continuous (faceMap (j := j) i) := by
  refine Continuous.subtype_mk (continuous_pi fun k => ?_) _
  refine Fin.succAboveCases i ?_ (fun k => ?_) k
  · simp only [Fin.insertNth_apply_same]
    exact continuous_const
  · simp only [Fin.insertNth_apply_succAbove]
    exact (continuous_apply k).comp continuous_subtype_val

theorem faceMap_injective (i : Fin (j + 2)) : Function.Injective (faceMap (j := j) i) := by
  intro x y h
  refine Subtype.ext (funext fun k => ?_)
  have := congrArg (fun z : stdSimplex ℝ (Fin (j + 2)) => z.1 (i.succAbove k)) h
  simpa using this

/-- The inverse of the `i`-th face inclusion, deleting the `i`-th coordinate. -/
def dropMap (i : Fin (j + 2)) {x : stdSimplex ℝ (Fin (j + 2))} (hx : x.1 i = 0) :
    stdSimplex ℝ (Fin (j + 1)) :=
  ⟨Fin.removeNth i x.1, fun k => x.2.1 _, by
    have h := x.2.2
    rw [Fin.sum_univ_succAbove _ i, hx, zero_add] at h
    exact h⟩

theorem faceMap_dropMap (i : Fin (j + 2)) {x : stdSimplex ℝ (Fin (j + 2))} (hx : x.1 i = 0) :
    faceMap i (dropMap i hx) = x := by
  refine Subtype.ext (funext fun k => ?_)
  refine Fin.succAboveCases i ?_ (fun k => ?_) k
  · rw [faceMap_coe_same, hx]
  · rw [faceMap_coe_succAbove]
    rfl

theorem dropMap_faceMap (i : Fin (j + 2)) (y : stdSimplex ℝ (Fin (j + 1))) :
    dropMap i (faceMap_coe_same i y) = y :=
  faceMap_injective i (faceMap_dropMap i (faceMap_coe_same i y))


end FiniteChains.TopologicalSingular
