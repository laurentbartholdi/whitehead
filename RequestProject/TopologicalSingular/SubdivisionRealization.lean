module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.SingularSubdivision
public import Mathlib.Topology.Algebra.Module.LinearMapPiProd

@[expose] public section

/-! # Iterated subdivision agrees with the explicit affine models -/


namespace FiniteChains.AffineVertexChains

open Set Topology VertexChains

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A : Set E} (hA : Convex ℝ A)

noncomputable def simplexLinearMap {n : ℕ} (v : Vertices A n) : (Fin (n + 1) → ℝ) →L[ℝ] E :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (v i).val

theorem simplexLinearMap_apply {n : ℕ} (v : Vertices A n) (z : Fin (n + 1) → ℝ) :
    simplexLinearMap v z = ∑ i, z i • (v i).val := by
  simp [simplexLinearMap]

include hA in
theorem simplexLinearMap_mapsTo {n : ℕ} (v : Vertices A n) :
    MapsTo (simplexLinearMap v) (TopologicalSingular.Domain n) A := by
  intro z hz
  rw [simplexLinearMap_apply]
  exact (affineEval hA v ⟨z, hz⟩).property

theorem restriction_simplexLinearMap {n : ℕ} (v : Vertices A n) :
    restriction (simplexLinearMap v) (simplexLinearMap_mapsTo hA v) = affineEval hA v := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  exact simplexLinearMap_apply v z.val

theorem affineEval_vertex {n : ℕ} (v : Vertices A n) (i : Fin (n + 1)) :
    affineEval hA v (stdSimplex.vertex i) = v i := by
  apply Subtype.ext
  simp [affineEval, Pi.single_apply]

theorem affineEval_vertices {n : ℕ} (v : Vertices A n) : affineEval hA v ∘ standardVertices n = v := by
  funext i
  exact affineEval_vertex hA v i

theorem subdivide_realize (n : ℕ) (c : VertexChains.Chain A n) :
    SingularSubdivision.subdivide n (realize hA n c) = realize hA n (subdivide (center hA) n c) := by
  have he : (SingularSubdivision.subdivide n).comp (realize hA n) =
      (realize hA n).comp (subdivide (center hA) n) := by
    apply VertexChains.linearMap_ext_basis
    intro v
    simp only [LinearMap.comp_apply, realize_single, SingularSubdivision.subdivide_single, one_smul]
    have hn := realize_subdivide_naturality (convex_stdSimplex ℝ (Fin (n + 1))) hA
      (simplexLinearMap v) (simplexLinearMap_mapsTo hA v) n (Finsupp.single (standardVertices n) 1)
    rw [restriction_simplexLinearMap, VertexChains.map_single, affineEval_vertices] at hn
    exact hn
  exact DFunLike.congr_fun he c

theorem iterated_subdivide_realize (k n : ℕ) (c : VertexChains.Chain A n) :
    ((SingularSubdivision.subdivide n)^[k]) (realize hA n c) =
      realize hA n (((subdivide (center hA) n)^[k]) c) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, subdivide_realize]

end FiniteChains.AffineVertexChains

namespace FiniteChains.SingularSubdivision

open TopologicalSingular AffineVertexChains

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

theorem iterated_subdivide_naturality (f : C(X, Y)) (k n : ℕ) (c : Chain X n) :
    TopologicalSingular.map f n (((subdivide n)^[k]) c) =
      ((subdivide n)^[k]) (TopologicalSingular.map f n c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, subdivide_naturality]

theorem iterated_subdivide_single_model (k n : ℕ) (σ : Simplex X n) :
    ((subdivide n)^[k]) (Finsupp.single σ 1) =
      TopologicalSingular.map σ n
        (realize (convex_stdSimplex ℝ (Fin (n + 1))) n
          (((VertexChains.subdivide (center (convex_stdSimplex ℝ (Fin (n + 1)))) n)^[k]) (generator n))) := by
  have hg : Finsupp.single σ 1 =
      TopologicalSingular.map σ n (realize (convex_stdSimplex ℝ (Fin (n + 1))) n (generator n)) := by
    rw [generator, realize_single, affineEval_standardVertices, map_single]
    rfl
  conv_lhs => rw [hg]
  rw [← iterated_subdivide_naturality, iterated_subdivide_realize]

end FiniteChains.SingularSubdivision
