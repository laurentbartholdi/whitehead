module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.SingularChainH0

@[expose] public section

/-! # Explicit triangle coordinates for singular path relations -/


set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular

open Set Topology

noncomputable def coordinate (n : ℕ) (i : Fin (n + 1)) : C(Domain n, unitInterval) :=
  ⟨fun z => ⟨z.val i, mem_Icc_of_mem_stdSimplex z.property i⟩,
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _⟩

theorem triangle_face_zero (z : Domain 1) :
    (stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) z).val = ![0, z.val 0, z.val 1] := by
  funext j
  simp only [stdSimplex.map, FunOnFinite.linearMap_apply_apply]
  change (∑ k : Fin 2 with (0 : Fin 3).succAbove k = j, z.val k) = _
  rw [Finset.sum_filter, Fin.sum_univ_two]
  fin_cases j <;> norm_num [Fin.succAbove, Fin.ext_iff, Fin.lt_def, Fin.le_def]

theorem triangle_face_one (z : Domain 1) :
    (stdSimplex.map (SimplexCategory.δ (1 : Fin 3)) z).val = ![z.val 0, 0, z.val 1] := by
  funext j
  simp only [stdSimplex.map, FunOnFinite.linearMap_apply_apply]
  change (∑ k : Fin 2 with (1 : Fin 3).succAbove k = j, z.val k) = _
  rw [Finset.sum_filter, Fin.sum_univ_two]
  fin_cases j <;> norm_num [Fin.succAbove, Fin.ext_iff, Fin.lt_def, Fin.le_def]

theorem triangle_face_two (z : Domain 1) :
    (stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) z).val = ![z.val 0, z.val 1, 0] := by
  funext j
  simp only [stdSimplex.map, FunOnFinite.linearMap_apply_apply]
  change (∑ k : Fin 2 with (2 : Fin 3).succAbove k = j, z.val k) = _
  rw [Finset.sum_filter, Fin.sum_univ_two]
  fin_cases j <;> norm_num [Fin.succAbove, Fin.ext_iff, Fin.lt_def, Fin.le_def]

noncomputable def squareTriangle0 : C(Domain 2, unitInterval × unitInterval) :=
  ⟨fun z => (coordinate 2 2 z, unitInterval.symm (coordinate 2 0 z)),
    (coordinate 2 2).continuous.prodMk (unitInterval.continuous_symm.comp (coordinate 2 0).continuous)⟩

noncomputable def squareTriangle1 : C(Domain 2, unitInterval × unitInterval) :=
  ⟨fun z => (unitInterval.symm (coordinate 2 0 z), coordinate 2 2 z),
    (unitInterval.continuous_symm.comp (coordinate 2 0).continuous).prodMk (coordinate 2 2).continuous⟩

theorem squareTriangle0_faces (z : Domain 1) :
    squareTriangle0 (stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) z) =
        (stdSimplexHomeomorphUnitInterval z, 1) ∧
    squareTriangle0 (stdSimplex.map (SimplexCategory.δ (1 : Fin 3)) z) =
        (stdSimplexHomeomorphUnitInterval z, stdSimplexHomeomorphUnitInterval z) ∧
    squareTriangle0 (stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) z) =
        (0, stdSimplexHomeomorphUnitInterval z) := by
  have hz := z.property.2
  rw [Fin.sum_univ_two] at hz
  refine ⟨?_, ?_, ?_⟩ <;>
    (apply Prod.ext <;> apply Subtype.ext <;>
      change _ = _ <;>
      simp only [squareTriangle0, ContinuousMap.coe_mk, coordinate, unitInterval.coe_symm_eq,
        triangle_face_zero, triangle_face_one, triangle_face_two,
        stdSimplexHomeomorphUnitInterval] <;>
      (dsimp [Matrix.vecHead, Matrix.vecTail]; all_goals linarith))

theorem squareTriangle1_faces (z : Domain 1) :
    squareTriangle1 (stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) z) =
        (1, stdSimplexHomeomorphUnitInterval z) ∧
    squareTriangle1 (stdSimplex.map (SimplexCategory.δ (1 : Fin 3)) z) =
        (stdSimplexHomeomorphUnitInterval z, stdSimplexHomeomorphUnitInterval z) ∧
    squareTriangle1 (stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) z) =
        (stdSimplexHomeomorphUnitInterval z, 0) := by
  have hz := z.property.2
  rw [Fin.sum_univ_two] at hz
  refine ⟨?_, ?_, ?_⟩ <;>
    (apply Prod.ext <;> apply Subtype.ext <;>
      change _ = _ <;>
      simp only [squareTriangle1, ContinuousMap.coe_mk, coordinate, unitInterval.coe_symm_eq,
        triangle_face_zero, triangle_face_one, triangle_face_two,
        stdSimplexHomeomorphUnitInterval] <;>
      (dsimp [Matrix.vecHead, Matrix.vecTail]; all_goals linarith))

end FiniteChains.TopologicalSingular
