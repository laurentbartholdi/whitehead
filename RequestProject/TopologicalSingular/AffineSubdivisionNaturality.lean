/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.AffineVertexChains
import RequestProject.TopologicalSingular.VertexSubdivisionHomotopy

/-! # Naturality of affine subdivision and its homotopy -/


namespace FiniteChains.AffineVertexChains

open Set Topology VertexChains

universe u v
variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {A : Set E} {B : Set F} (hA : Convex ℝ A) (hB : Convex ℝ B)

theorem realize_subdivide_naturality (f : E →L[ℝ] F) (hf : MapsTo f A B) (n : ℕ)
    (c : VertexChains.Chain A n) :
    TopologicalSingular.map (restriction f hf) n (realize hA n (subdivide (center hA) n c)) =
      realize hB n (subdivide (center hB) n (VertexChains.map (restriction f hf) n c)) := by
  rw [realize_naturality hA hB]
  have he := DFunLike.congr_fun
    (subdivide_naturality (center hA) (center hB) (restriction f hf)
      (center_naturality hA hB f hf) n) c
  dsimp only [LinearMap.comp_apply] at he
  rw [he]

theorem realize_subdivideHomotopy_naturality (f : E →L[ℝ] F) (hf : MapsTo f A B) (n : ℕ)
    (c : VertexChains.Chain A n) :
    TopologicalSingular.map (restriction f hf) (n + 1)
        (realize hA (n + 1) (subdivideHomotopy (center hA) n c)) =
      realize hB (n + 1) (subdivideHomotopy (center hB) n (VertexChains.map (restriction f hf) n c)) := by
  rw [realize_naturality hA hB]
  have he := DFunLike.congr_fun
    (subdivideHomotopy_naturality (center hA) (center hB) (restriction f hf)
      (center_naturality hA hB f hf) n) c
  dsimp only [LinearMap.comp_apply] at he
  rw [he]

noncomputable def standardMap {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    C(TopologicalSingular.Domain m, TopologicalSingular.Domain n) :=
  ⟨stdSimplex.map f, stdSimplex.continuous_map f⟩

noncomputable def standardLinearMap {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    (Fin (m + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ⟨FunOnFinite.linearMap ℝ ℝ f, FunOnFinite.continuous_linearMap ℝ ℝ f⟩

theorem standardLinearMap_mapsTo {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    MapsTo (standardLinearMap f) (TopologicalSingular.Domain m) (TopologicalSingular.Domain n) := by
  intro z hz
  exact (stdSimplex.map f ⟨z, hz⟩).property

theorem restriction_standardLinearMap {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    restriction (standardLinearMap f) (standardLinearMap_mapsTo f) = standardMap f := rfl

theorem standardMap_vertices {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    standardMap f ∘ standardVertices m = standardVertices n ∘ f := by
  funext i
  exact stdSimplex.map_vertex f i

theorem realize_standard_subdivide_naturality {d e k : ℕ}
    (f : Fin (d + 1) → Fin (e + 1)) (c : VertexChains.Chain (TopologicalSingular.Domain d) k) :
    TopologicalSingular.map (standardMap f) k
        (realize (convex_stdSimplex ℝ (Fin (d + 1))) k
          (subdivide (center (convex_stdSimplex ℝ (Fin (d + 1)))) k c)) =
      realize (convex_stdSimplex ℝ (Fin (e + 1))) k
        (subdivide (center (convex_stdSimplex ℝ (Fin (e + 1)))) k
          (VertexChains.map (standardMap f) k c)) :=
  realize_subdivide_naturality _ _ (standardLinearMap f) (standardLinearMap_mapsTo f) k c

theorem realize_standard_homotopy_naturality {d e k : ℕ}
    (f : Fin (d + 1) → Fin (e + 1)) (c : VertexChains.Chain (TopologicalSingular.Domain d) k) :
    TopologicalSingular.map (standardMap f) (k + 1)
        (realize (convex_stdSimplex ℝ (Fin (d + 1))) (k + 1)
          (subdivideHomotopy (center (convex_stdSimplex ℝ (Fin (d + 1)))) k c)) =
      realize (convex_stdSimplex ℝ (Fin (e + 1))) (k + 1)
        (subdivideHomotopy (center (convex_stdSimplex ℝ (Fin (e + 1)))) k
          (VertexChains.map (standardMap f) k c)) :=
  realize_subdivideHomotopy_naturality _ _ (standardLinearMap f) (standardLinearMap_mapsTo f) k c

end FiniteChains.AffineVertexChains
