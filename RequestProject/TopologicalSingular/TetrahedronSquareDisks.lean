module

public import RequestProject.TopologicalSingular.SimplexFaceIntersections

@[expose] public section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology

/-- The two faces meeting along the edge `03`, parametrized by a square.
Its corners in cyclic order are the vertices `0,1,3,2`. -/
noncomputable def tetrahedronDisk03 : C((Fin 2 → I), Domain 3) where
  toFun z := ⟨![1 - max (z 0 : ℝ) (z 1 : ℝ), max ((z 0 : ℝ) - z 1) 0,
    max ((z 1 : ℝ) - z 0) 0, min (z 0 : ℝ) (z 1 : ℝ)], by
    constructor
    · intro i
      fin_cases i
      · exact sub_nonneg.mpr (max_le (z 0).property.2 (z 1).property.2)
      · exact le_max_right _ _
      · exact le_max_right _ _
      · exact le_min (z 0).property.1 (z 1).property.1
    · simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Fin.sum_univ_zero, add_zero]
      rcases le_total (z 0 : ℝ) (z 1 : ℝ) with h | h
      · rw [max_eq_right h, max_eq_right (sub_nonpos.mpr h),
          max_eq_left (sub_nonneg.mpr h), min_eq_left h]
        ring
      · rw [max_eq_left h, max_eq_left (sub_nonneg.mpr h),
          max_eq_right (sub_nonpos.mpr h), min_eq_right h]
        ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const.sub
        (((continuous_apply 0).subtype_val).max ((continuous_apply 1).subtype_val))
    · exact (((continuous_apply 0).subtype_val).sub
        ((continuous_apply 1).subtype_val)).max continuous_const
    · exact (((continuous_apply 1).subtype_val).sub
        ((continuous_apply 0).subtype_val)).max continuous_const
    · exact ((continuous_apply 0).subtype_val).min ((continuous_apply 1).subtype_val)

/-- The other two faces of the tetrahedron, meeting along `12`, with the same
boundary parametrization and the other diagonal of the square. -/
noncomputable def tetrahedronDisk12 : C((Fin 2 → I), Domain 3) where
  toFun z := ⟨![max (1 - (z 0 : ℝ) - z 1) 0, min (z 0 : ℝ) (1 - z 1),
    min (z 1 : ℝ) (1 - z 0), max ((z 0 : ℝ) + z 1 - 1) 0], by
    constructor
    · intro i
      fin_cases i
      · exact le_max_right _ _
      · exact le_min (z 0).property.1 (sub_nonneg.mpr (z 1).property.2)
      · exact le_min (z 1).property.1 (sub_nonneg.mpr (z 0).property.2)
      · exact le_max_right _ _
    · simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Fin.sum_univ_zero, add_zero]
      by_cases h : (z 0 : ℝ) + z 1 ≤ 1
      · rw [max_eq_left (by linarith), min_eq_left (by linarith),
          min_eq_left (by linarith), max_eq_right (by linarith)]
        ring
      · rw [max_eq_right (by linarith), min_eq_right (by linarith),
          min_eq_right (by linarith), max_eq_left (by linarith)]
        ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact ((continuous_const.sub ((continuous_apply 0).subtype_val)).sub
        ((continuous_apply 1).subtype_val)).max continuous_const
    · exact ((continuous_apply 0).subtype_val).min
        (continuous_const.sub ((continuous_apply 1).subtype_val))
    · exact ((continuous_apply 1).subtype_val).min
        (continuous_const.sub ((continuous_apply 0).subtype_val))
    · exact ((((continuous_apply 0).subtype_val).add
        ((continuous_apply 1).subtype_val)).sub continuous_const).max continuous_const

theorem tetrahedronDisk03_faces (z : Fin 2 → I) :
    (tetrahedronDisk03 z).val 1 = 0 ∨ (tetrahedronDisk03 z).val 2 = 0 := by
  rcases le_total (z 0 : ℝ) (z 1 : ℝ) with h | h
  · exact Or.inl (max_eq_right (sub_nonpos.mpr h))
  · exact Or.inr (max_eq_right (sub_nonpos.mpr h))

theorem tetrahedronDisk12_faces (z : Fin 2 → I) :
    (tetrahedronDisk12 z).val 0 = 0 ∨ (tetrahedronDisk12 z).val 3 = 0 := by
  by_cases h : (z 0 : ℝ) + z 1 ≤ 1
  · exact Or.inr (max_eq_right (by linarith))
  · exact Or.inl (max_eq_right (by linarith))

theorem tetrahedronDisks_boundary_eq (z : Fin 2 → I) (hz : z ∈ Cube.boundary (Fin 2)) :
    tetrahedronDisk03 z = tetrahedronDisk12 z := by
  obtain ⟨i, hi⟩ := hz
  have h0 := (z 0).property
  have h1 := (z 1).property
  apply Subtype.ext
  change ![1 - max (z 0 : ℝ) (z 1 : ℝ), max ((z 0 : ℝ) - z 1) 0,
      max ((z 1 : ℝ) - z 0) 0, min (z 0 : ℝ) (z 1 : ℝ)] =
    ![max (1 - (z 0 : ℝ) - z 1) 0, min (z 0 : ℝ) (1 - z 1),
      min (z 1 : ℝ) (1 - z 0), max ((z 0 : ℝ) + z 1 - 1) 0]
  funext j
  fin_cases i <;> rcases hi with hi | hi <;> fin_cases j <;>
    dsimp at hi ⊢ <;> norm_num [hi] <;>
    simp only [max_def, min_def] <;> split_ifs <;> linarith [h0.1, h0.2, h1.1, h1.2]

end FiniteChains.TopologicalSingular
