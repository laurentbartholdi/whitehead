module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.AffineSubdivisionGeometry

@[expose] public section

/-! # Barycentric subdivision strictly decreases mesh

Every vertex tuple in the support has the proved smaller diameter bound.
The estimate includes cancellations, repeated vertices and degree zero.
-/


namespace FiniteChains.AffineVertexChains

open Set Topology VertexChains

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A : Set E} (hA : Convex ℝ A)

def MeshBound {n : ℕ} (v : Vertices A n) (D : ℝ) : Prop :=
  ∀ i j, dist (v i).val (v j).val ≤ D

noncomputable def meshChains (n : ℕ) (D : ℝ) : Submodule ℤ (VertexChains.Chain A n) :=
  Finsupp.supported ℤ ℤ {v | MeshBound v D}

theorem shrink_le_succ (n : ℕ) : shrink n ≤ shrink (n + 1) := by
  simp only [shrink, Nat.cast_add, Nat.cast_one]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

theorem subdivide_single_mem_mesh (n : ℕ) (v : Vertices A n) (D : ℝ) (hD₀ : 0 ≤ D)
    (hD : MeshBound v D) :
    subdivide (center hA) n (Finsupp.single v 1) ∈ meshChains n (shrink n * D) := by
  induction n generalizing D with
  | zero =>
    rw [subdivide_zero]
    refine Finsupp.single_mem_supported ℤ 1 ?_
    intro i j
    have hij : i = j := by apply Fin.ext; omega
    rw [hij, dist_self]
    simp [shrink]
  | succ n ih =>
    rw [subdivide_succ_single, one_smul, VertexChains.boundary_single]
    simp only [map_sum, map_zsmul]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply map_mem_of_supported
      {w : Vertices A n | (∀ j, (w j).val ∈ convexHull ℝ (Set.range (fun j => (v j).val))) ∧
        MeshBound w (shrink n * D)} _ (cone (center hA (n + 1) v) n) ?_ ?_
    · intro w hw
      rw [cone_single]
      refine Finsupp.single_mem_supported ℤ 1 ?_
      intro a b
      refine Fin.cases ?_ (fun a => ?_) a
      · refine Fin.cases ?_ (fun b => ?_) b
        · simpa only [dist_self] using mul_nonneg (shrink_nonneg (n + 1)) hD₀
        · exact center_dist_convexHull_le hA v D hD (hw.1 b)
      · refine Fin.cases ?_ (fun b => ?_) b
        · rw [dist_comm]
          exact center_dist_convexHull_le hA v D hD (hw.1 a)
        · exact (hw.2 a b).trans (mul_le_mul_of_nonneg_right (shrink_le_succ n) hD₀)
    · intro w hw
      refine ⟨?_, (ih (face i v) D hD₀ (fun a b => hD (i.succAbove a) (i.succAbove b))) hw⟩
      intro j
      apply convexHull_mono ?_ (subdivide_vertices_mem_convexHull hA (face i v) hw j)
      rintro x ⟨k, rfl⟩
      exact ⟨i.succAbove k, rfl⟩

theorem subdivide_mem_mesh (n : ℕ) (D : ℝ) (hD₀ : 0 ≤ D) {c : VertexChains.Chain A n}
    (hc : c ∈ meshChains n D) : subdivide (center hA) n c ∈ meshChains n (shrink n * D) :=
  map_mem_of_supported _ _ (subdivide (center hA) n)
    (fun v hv => subdivide_single_mem_mesh hA n v D hD₀ hv) hc

theorem iterated_subdivide_mem_mesh (k n : ℕ) (D : ℝ) (hD₀ : 0 ≤ D) {c : VertexChains.Chain A n}
    (hc : c ∈ meshChains n D) :
    ((subdivide (center hA) n)^[k]) c ∈ meshChains n ((shrink n) ^ k * D) := by
  induction k with
  | zero => simpa using hc
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have he := subdivide_mem_mesh hA n ((shrink n) ^ k * D)
      (mul_nonneg (pow_nonneg (shrink_nonneg n) k) hD₀) ih
    simpa only [pow_succ', mul_assoc] using he

theorem subdivide_realized_mesh_bound {n : ℕ} (v : Vertices A n) (D : ℝ) (hD₀ : 0 ≤ D)
    (hD : MeshBound v D) {w : Vertices A n}
    (hw : w ∈ (subdivide (center hA) n (Finsupp.single v 1)).support)
    (z t : TopologicalSingular.Domain n) :
    dist (affineEval hA w z).val (affineEval hA w t).val ≤ shrink n * D :=
  affineEval_dist_le hA w (shrink n * D) ((subdivide_single_mem_mesh hA n v D hD₀ hD) hw) z t

end FiniteChains.AffineVertexChains
