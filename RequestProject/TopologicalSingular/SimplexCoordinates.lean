module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

namespace FiniteChains.TopologicalSingular

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The finite-support simplex and the barycentric-coordinate simplex have the same topology. -/
noncomputable def simplexCoordinates (n : ℕ) :
    Convexity.StdSimplex ℝ (Fin (n + 1)) ≃ₜ stdSimplex ℝ (Fin (n + 1)) :=
  (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).toHomeomorph.trans
    (Homeomorph.setCongr (by
      rw [Convexity.StdSimplex.range_toFun_comp_weights]
      ext x
      simp [stdSimplex]))

@[simp] theorem simplexCoordinates_apply (n : ℕ)
    (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    (simplexCoordinates n z).val = z.weights := rfl

/-- Barycentric coordinates commute with maps of vertex sets. -/
theorem simplexCoordinates_map {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1))
    (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    simplexCoordinates m (Convexity.StdSimplex.map f z) =
      stdSimplex.map f (simplexCoordinates n z) := by
  apply Subtype.ext
  funext i
  change (Finsupp.mapDomain f z.weights) i = (FunOnFinite.linearMap ℝ ℝ f z.weights) i
  simp [FunOnFinite.linearMap_apply_apply, Finsupp.mapDomain_apply,
    Finsupp.sum_fintype, Finsupp.single_apply, Finset.sum_filter, eq_comm]

@[simp] theorem simplexCoordinates_symm_weights_apply (n : ℕ)
    (z : stdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    ((simplexCoordinates n).symm z).weights i = z.val i := by
  exact congrArg (fun w : stdSimplex ℝ (Fin (n + 1)) => w.val i)
    ((simplexCoordinates n).apply_symm_apply z)

end FiniteChains.TopologicalSingular
