import RequestProject.TopologicalSingular.SimplexHornFiller
import RequestProject.TopologicalSingular.StickTriangleComparison

namespace FiniteChains.TopologicalSingular
variable {X : Type} [TopologicalSpace X] {n : ℕ}

/-- Fill a horn using the actual singular-simplex and face operators of this
project. Agreement is required only where the prescribed faces intersect. -/
theorem singular_horn_filler_exists (i : Fin (n + 2))
    (g : ∀ j : Fin (n + 2), j ≠ i → Simplex X n)
    (hg : ∀ (j k : Fin (n + 2)) (hj : j ≠ i) (hk : k ≠ i)
      (z w : Domain n),
      stdSimplex.map (SimplexCategory.δ j) z = stdSimplex.map (SimplexCategory.δ k) w →
      g j hj z = g k hk w) :
    ∃ tau : Simplex X (n + 1), ∀ (j : Fin (n + 2)) (hj : j ≠ i), face j tau = g j hj := by
  let faces : Fin (n + 1) → Simplex X n :=
    fun k => g (i.succAbove k) (Fin.succAbove_ne i k)
  have hfaces : SimplexHornFaceCompatible i faces := by
    intro j k z w h
    apply hg (i.succAbove j) (i.succAbove k)
    simpa only [simplex_face_eq_faceMap] using h
  let tau : Simplex X (n + 1) := simplexHornFiller i faces hfaces
  refine ⟨tau, ?_⟩
  intro j hj
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
  apply ContinuousMap.ext
  intro z
  change tau (stdSimplex.map (SimplexCategory.δ (i.succAbove k)) z) = faces k z
  rw [simplex_face_eq_faceMap]
  exact simplexHornFiller_face i faces hfaces k z

end FiniteChains.TopologicalSingular
