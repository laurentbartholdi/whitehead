import RequestProject.TopologicalSingular.SimplexFaceIntersections
import RequestProject.TopologicalSingular.CoherentPrism

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ}

variable (lo : Simplex X n → Simplex X n)
  (hi : Simplex X (n + 1) → Simplex X (n + 1))
  (L : ∀ tau : Simplex X n, tau.Homotopy (lo tau))
  (H : ∀ tau : Simplex X (n + 1), tau.Homotopy (hi tau))
  (compat : ∀ (tau : Simplex X (n + 1)) (i : Fin (n + 2)) (t : I) (z : Domain n),
    H tau (t, stdSimplex.map (SimplexCategory.δ i) z) = L (face i tau) (t, z))

include compat

/-- Facewise homotopies that agree with one fixed lower-dimensional family
agree on all intersections, including higher-codimension intersections. -/
theorem compatibleFaceHomotopies_coherent (tau : Simplex X (n + 2))
    (i j : Fin (n + 3)) (t : I) (z w : Domain (n + 1))
    (h : stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w) :
    H (face i tau) (t, z) = H (face j tau) (t, w) := by
  by_cases hij : i = j
  · subst j
    rw [simplex_face_injective i h]
  · obtain ⟨k, l, q, hz, hw, he⟩ := simplex_face_intersection_factor i j hij z w h
    have hf : face k (face i tau) = face l (face j tau) := by
      apply ContinuousMap.ext
      intro a
      simp only [face_apply, he a]
    rw [hz, hw, compat, compat, hf]

/-- A coherent family through dimension `n+1` extends over every simplex of
dimension `n+2`, while preserving the chosen homotopies on its faces exactly. -/
theorem compatibleSimplexHomotopyExtension_exists (tau : Simplex X (n + 2)) :
    ∃ g : Simplex X (n + 2), ∃ F : tau.Homotopy g,
      ∀ (i : Fin (n + 3)) (t : I) (z : Domain (n + 1)),
        F (t, stdSimplex.map (SimplexCategory.δ i) z) = H (face i tau) (t, z) :=
  simplex_face_homotopy_extension tau (fun i => (H (face i tau)).toContinuousMap)
    (compatibleFaceHomotopies_coherent lo hi L H compat tau)
    (fun i z => (H (face i tau)).apply_zero z)

end FiniteChains.TopologicalSingular
