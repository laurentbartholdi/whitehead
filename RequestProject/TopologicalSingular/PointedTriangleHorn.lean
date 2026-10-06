module

public import RequestProject.TopologicalSingular.PointedSingularTriangle

@[expose] public section

namespace FiniteChains.TopologicalSingular
variable {X : Type} [TopologicalSpace X] {x : X}

/-- Fill three pointed triangles and verify that every edge of the filler,
including the edges of its missing triangular face, is constant. -/
theorem pointed_triangle_horn_exists (i : Fin 4)
    (a : Fin 4 → PointedSingularTriangle X x) :
    ∃ tau : Simplex X 3,
      (∀ (j : Fin 4) (_hj : j ≠ i), face j tau = (a j).map) ∧
      (∀ (j : Fin 4) (k : Fin 3),
        face k (face j tau) = ContinuousMap.const (Domain 1) x) := by
  obtain ⟨tau, htau⟩ := singular_horn_filler_of_face_compatible i
    (fun j _ => (a j).map) (by
      intro j k hj hk
      rw [(a j).based, (a (j.succAbove k)).based])
  refine ⟨tau, htau, ?_⟩
  intro j k
  by_cases hj : j = i
  · subst j
    rw [singular_double_face_swap tau i k,
      htau (i.succAbove k) (Fin.succAbove_ne i k), (a (i.succAbove k)).based]
  · rw [htau j hj, (a j).based]

end FiniteChains.TopologicalSingular
