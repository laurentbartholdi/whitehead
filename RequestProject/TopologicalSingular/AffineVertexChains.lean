module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.VertexSubdivision
public import RequestProject.TopologicalSingular.SingularChainMaps
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Normed.Module.Basic

@[expose] public section

/-! # Realization of vertex chains as affine singular simplices

All vertices lie in an actual convex subspace of a real normed space.
The realization is continuous, respects every face, and carries the
formal boundary to the actual singular boundary. The chosen centers are
the genuine equally weighted barycenters.
-/


set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.AffineVertexChains

open Set Topology VertexChains

universe u v
variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {A : Set E} {B : Set F} (hA : Convex ℝ A) (hB : Convex ℝ B)

noncomputable def affineEval {n : ℕ} (v : Vertices A n) : TopologicalSingular.Simplex A n :=
  ⟨fun z => ⟨∑ i, z.val i • (v i).val,
    hA.sum_mem (fun i _ => z.property.1 i) z.property.2 (fun i _ => (v i).property)⟩, by
    apply Continuous.subtype_mk
    apply continuous_finset_sum
    intro i _
    exact ((continuous_apply i).comp continuous_subtype_val).smul continuous_const⟩

theorem affineEval_apply {n : ℕ} (v : Vertices A n) (z : TopologicalSingular.Domain n) :
    (affineEval hA v z).val = ∑ i, z.val i • (v i).val := rfl

theorem affineEval_reindex {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (v : Vertices A n) (z : TopologicalSingular.Domain m) :
    affineEval hA (v ∘ f) z = affineEval hA v (stdSimplex.map f z) := by
  classical
  apply Subtype.ext
  change (∑ i, z.val i • (v (f i)).val) = ∑ j, (stdSimplex.map f z).val j • (v j).val
  symm
  calc
    _ = ∑ j, ∑ i ∈ Finset.univ.filter (fun i => f i = j), z.val i • (v (f i)).val := by
      apply Finset.sum_congr rfl
      intro j _
      change (FunOnFinite.linearMap ℝ ℝ f z.val) j • (v j).val = _
      rw [FunOnFinite.linearMap_apply_apply, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise Finset.univ f (fun i => z.val i • (v (f i)).val)

theorem face_affineEval {n : ℕ} (i : Fin (n + 2)) (v : Vertices A (n + 1)) :
    TopologicalSingular.face i (affineEval hA v) = affineEval hA (face i v) := by
  apply ContinuousMap.ext
  intro z
  exact (affineEval_reindex hA i.succAbove v z).symm

noncomputable def realize (n : ℕ) : VertexChains.Chain A n →ₗ[ℤ] TopologicalSingular.Chain A n :=
  Finsupp.lmapDomain ℤ ℤ (affineEval hA)

@[simp] theorem realize_single (n : ℕ) (v : Vertices A n) (r : ℤ) :
    realize hA n (Finsupp.single v r) = Finsupp.single (affineEval hA v) r :=
  Finsupp.mapDomain_single

theorem realize_boundary (n : ℕ) (c : VertexChains.Chain A (n + 1)) :
    realize hA n (VertexChains.boundary n c) = TopologicalSingular.boundary n (realize hA (n + 1) c) := by
  have he : (realize hA n).comp (VertexChains.boundary n) =
      (TopologicalSingular.boundary n).comp (realize hA (n + 1)) := by
    apply Finsupp.lhom_ext
    intro v r
    simp only [LinearMap.comp_apply, VertexChains.boundary_single, realize_single,
      TopologicalSingular.boundary_single, map_sum, map_zsmul, face_affineEval]
  exact DFunLike.congr_fun he c

noncomputable def center (n : ℕ) (v : Vertices A n) : A := affineEval hA v stdSimplex.barycenter

theorem center_val (n : ℕ) (v : Vertices A n) :
    (center hA n v).val = ∑ i, ((n + 1 : ℕ) : ℝ)⁻¹ • (v i).val := by
  simp only [center, affineEval_apply, stdSimplex.barycenter_apply, Fintype.card_fin]

def restriction (f : E →L[ℝ] F) (hf : MapsTo f A B) : C(A, B) :=
  ⟨fun a => ⟨f a.val, hf a.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem affineEval_naturality (f : E →L[ℝ] F) (hf : MapsTo f A B) {n : ℕ} (v : Vertices A n) :
    TopologicalSingular.simplexMap (restriction f hf) n (affineEval hA v) =
      affineEval hB (restriction f hf ∘ v) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  change f (∑ i, z.val i • (v i).val) = ∑ i, z.val i • f (v i).val
  simp only [map_sum, map_smul]

theorem center_naturality (f : E →L[ℝ] F) (hf : MapsTo f A B) (n : ℕ) (v : Vertices A n) :
    restriction f hf (center hA n v) = center hB n (restriction f hf ∘ v) :=
  DFunLike.congr_fun (affineEval_naturality hA hB f hf v) stdSimplex.barycenter

theorem realize_naturality (f : E →L[ℝ] F) (hf : MapsTo f A B) (n : ℕ)
    (c : VertexChains.Chain A n) :
    TopologicalSingular.map (restriction f hf) n (realize hA n c) =
      realize hB n (VertexChains.map (restriction f hf) n c) := by
  have he : (TopologicalSingular.map (restriction f hf) n).comp (realize hA n) =
      (realize hB n).comp (VertexChains.map (restriction f hf) n) := by
    apply Finsupp.lhom_ext
    intro v r
    simp only [LinearMap.comp_apply, realize_single, TopologicalSingular.map_single,
      VertexChains.map_single]
    rw [affineEval_naturality hA hB f hf]
  exact DFunLike.congr_fun he c

noncomputable def standardVertices (d : ℕ) : Vertices (TopologicalSingular.Domain d) d :=
  fun i => stdSimplex.vertex i

theorem affineEval_standardVertices (d : ℕ) :
    affineEval (convex_stdSimplex ℝ (Fin (d + 1))) (standardVertices d) =
      ContinuousMap.id (TopologicalSingular.Domain d) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  funext j
  simp [affineEval, standardVertices, Finset.sum_apply, Pi.single_apply]

end FiniteChains.AffineVertexChains
