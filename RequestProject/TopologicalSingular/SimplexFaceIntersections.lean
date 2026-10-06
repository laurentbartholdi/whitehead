import RequestProject.TopologicalSingular.TriangleBasedNormalization

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ}

/-- The two orders of inserting the missing coordinates give the same face. -/
theorem simplex_double_face_swap (i : Fin (n + 3)) (k : Fin (n + 2)) (q : Domain n) :
    stdSimplex.map (SimplexCategory.δ i) (stdSimplex.map (SimplexCategory.δ k) q) =
      stdSimplex.map (SimplexCategory.δ (i.succAbove k))
        (stdSimplex.map (SimplexCategory.δ (k.predAbove i)) q) := by
  change stdSimplex.map i.succAbove (stdSimplex.map k.succAbove q) =
    stdSimplex.map (i.succAbove k).succAbove (stdSimplex.map (k.predAbove i).succAbove q)
  rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
  have he : i.succAbove ∘ k.succAbove =
      (i.succAbove k).succAbove ∘ (k.predAbove i).succAbove := by
    funext a
    exact (Fin.succAbove_succAbove_succAbove_predAbove i k a).symm
  rw [he]

theorem singular_double_face_swap (tau : Simplex X (n + 2))
    (i : Fin (n + 3)) (k : Fin (n + 2)) :
    face k (face i tau) = face (k.predAbove i) (face (i.succAbove k) tau) := by
  apply ContinuousMap.ext
  intro q
  simp only [face_apply, simplex_double_face_swap i k q]

/-- A point in two different faces comes from one common codimension-two face,
with a single parameter in the lower-dimensional simplex. -/
theorem simplex_face_intersection_factor (i j : Fin (n + 3)) (hij : i ≠ j)
    (z w : Domain (n + 1))
    (h : stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w) :
    ∃ (k l : Fin (n + 2)) (q : Domain n),
      z = stdSimplex.map (SimplexCategory.δ k) q ∧
      w = stdSimplex.map (SimplexCategory.δ l) q ∧
      ∀ a : Domain n,
        stdSimplex.map (SimplexCategory.δ i) (stdSimplex.map (SimplexCategory.δ k) a) =
          stdSimplex.map (SimplexCategory.δ j) (stdSimplex.map (SimplexCategory.δ l) a) := by
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
  have hz : z.val k = 0 := by
    rw [← simplex_face_coordinate_succAbove i z k, hk, h]
    exact simplex_face_coordinate_zero j w
  obtain ⟨q, hq⟩ := domain_zero_coordinate_face z k hz
  have he (a : Domain n) := simplex_double_face_swap i k a
  rw [hk] at he
  refine ⟨k, k.predAbove i, q, hq.symm, ?_, he⟩
  apply simplex_face_injective j
  rw [← h, ← hq]
  exact he q

end FiniteChains.TopologicalSingular
