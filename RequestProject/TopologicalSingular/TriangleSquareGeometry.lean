module

public import RequestProject.TopologicalSingular.SquareSingularChains

@[expose] public section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology

/-- A zero barycentric coordinate identifies an actual point of that face. -/
theorem domain_zero_coordinate_face {n : ℕ} (z : Domain (n + 1)) (i : Fin (n + 2))
    (hi : z.val i = 0) : ∃ w : Domain n, stdSimplex.map (SimplexCategory.δ i) w = z := by
  let w : Domain n := ⟨fun j => z.val (i.succAbove j), fun j => z.property.1 _, by
    have hs := z.property.2
    rw [Fin.sum_univ_succAbove (fun j => z.val j) i, hi, zero_add] at hs
    exact hs⟩
  refine ⟨w, ?_⟩
  apply Subtype.ext
  funext k
  change (FunOnFinite.linearMap ℝ ℝ i.succAbove w.val) k = z.val k
  rw [FunOnFinite.linearMap_apply_apply]
  by_cases hk : k = i
  · subst k
    simp [Fin.succAbove_ne, hi]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
    simp [w, Finset.sum_filter]

/-- Collapse the upper triangle of the square onto an edge of the standard
triangle. On the lower triangle this map is exactly the identity simplex. -/
noncomputable def squareToTriangle : C((Fin 2 → I), Domain 2) where
  toFun z := ⟨![1 - (z 0 : ℝ), max ((z 0 : ℝ) - z 1) 0, min (z 0 : ℝ) (z 1 : ℝ)], by
    constructor
    · intro i
      fin_cases i
      · exact sub_nonneg.mpr (z 0).property.2
      · exact le_max_right _ _
      · exact le_min (z 0).property.1 (z 1).property.1
    · rw [Fin.sum_univ_three]
      change 1 - (z 0 : ℝ) + max ((z 0 : ℝ) - z 1) 0 + min (z 0 : ℝ) (z 1 : ℝ) = 1
      rcases le_total (z 0 : ℝ) (z 1 : ℝ) with h | h
      · rw [max_eq_right (sub_nonpos.mpr h), min_eq_left h]
        ring
      · rw [max_eq_left (sub_nonneg.mpr h), min_eq_right h]
        ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const.sub ((continuous_apply 0).subtype_val)
    · exact (((continuous_apply 0).subtype_val).sub ((continuous_apply 1).subtype_val)).max continuous_const
    · exact ((continuous_apply 0).subtype_val).min ((continuous_apply 1).subtype_val)

theorem squareToTriangle_triangle1 (z : Domain 2) : squareToTriangle (cubeTriangle1 z) = z := by
  have hs : z.val 0 + z.val 1 + z.val 2 = 1 := by
    exact (Fin.sum_univ_three z.val).symm.trans z.property.2
  have h : z.val 2 ≤ 1 - z.val 0 := by linarith [z.property.1 1]
  apply Subtype.ext
  change ![1 - (1 - z.val 0), max ((1 - z.val 0) - z.val 2) 0,
    min (1 - z.val 0) (z.val 2)] = z.val
  funext i
  fin_cases i
  · change 1 - (1 - z.val 0) = z.val 0
    ring
  · change max ((1 - z.val 0) - z.val 2) 0 = z.val 1
    rw [max_eq_left (sub_nonneg.mpr h)]
    linarith
  · exact min_eq_right h

theorem squareToTriangle_triangle0_zero (z : Domain 2) :
    (squareToTriangle (cubeTriangle0 z)).val 1 = 0 := by
  have hs : z.val 0 + z.val 1 + z.val 2 = 1 := by
    exact (Fin.sum_univ_three z.val).symm.trans z.property.2
  change max (z.val 2 - (1 - z.val 0)) 0 = 0
  apply max_eq_right
  linarith [z.property.1 1]

theorem squareToTriangle_boundary (z : Fin 2 → I) (hz : z ∈ Cube.boundary (Fin 2)) :
    ∃ i : Fin 3, (squareToTriangle z).val i = 0 := by
  obtain ⟨i, hi⟩ := hz
  fin_cases i
  · rcases hi with hi | hi
    · refine ⟨2, ?_⟩
      change z 0 = 0 at hi
      change min (z 0 : ℝ) (z 1 : ℝ) = 0
      rw [hi]
      exact min_eq_left (z 1).property.1
    · refine ⟨0, ?_⟩
      change z 0 = 1 at hi
      change 1 - (z 0 : ℝ) = 0
      rw [hi]
      exact sub_self _
  · rcases hi with hi | hi
    · refine ⟨2, ?_⟩
      change z 1 = 0 at hi
      change min (z 0 : ℝ) (z 1 : ℝ) = 0
      rw [hi]
      exact min_eq_right (z 0).property.1
    · refine ⟨1, ?_⟩
      change z 1 = 1 at hi
      change max ((z 0 : ℝ) - z 1) 0 = 0
      rw [hi]
      exact max_eq_right (sub_nonpos.mpr (z 0).property.2)

end FiniteChains.TopologicalSingular
