/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.AffineVertexChains
import RequestProject.TopologicalSingular.VertexCarriers
import Mathlib.Analysis.Normed.Module.Convex

/-! # Convex carriers and barycenter distance estimates

Subdivision and its chain homotopy stay in the original convex hull.
The barycenter of n+1 vertices is at distance at most n/(n+1) times their
diameter bound from every point of that hull. No excision is assumed.
-/


namespace FiniteChains.AffineVertexChains

open Set Topology VertexChains

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A : Set E} (hA : Convex ℝ A)

theorem affineEval_mem_of_vertices {S : Set E} (hS : Convex ℝ S) {n : ℕ}
    (v : Vertices A n) (hv : ∀ i, (v i).val ∈ S) (z : TopologicalSingular.Domain n) :
    (affineEval hA v z).val ∈ S :=
  hS.sum_mem (fun i _ => z.property.1 i) z.property.2 (fun i _ => hv i)

theorem center_mem_of_vertices {S : Set E} (hS : Convex ℝ S) (n : ℕ)
    (v : Vertices A n) (hv : ∀ i, (v i).val ∈ S) : (center hA n v).val ∈ S :=
  affineEval_mem_of_vertices hA hS v hv stdSimplex.barycenter

theorem subdivide_mem_convex_carrier {S : Set E} (hS : Convex ℝ S) (n : ℕ)
    {c : VertexChains.Chain A n} (hc : c ∈ carried {x : A | x.val ∈ S} n) :
    subdivide (center hA) n c ∈ carried {x : A | x.val ∈ S} n :=
  subdivide_mem_carried (center hA) _ (fun n v hv => center_mem_of_vertices hA hS n v hv) n hc

theorem homotopy_mem_convex_carrier {S : Set E} (hS : Convex ℝ S) (n : ℕ)
    {c : VertexChains.Chain A n} (hc : c ∈ carried {x : A | x.val ∈ S} n) :
    subdivideHomotopy (center hA) n c ∈ carried {x : A | x.val ∈ S} (n + 1) :=
  subdivideHomotopy_mem_carried (center hA) _ (fun n v hv => center_mem_of_vertices hA hS n v hv) n hc

theorem subdivide_vertices_mem_convexHull {n : ℕ} (v : Vertices A n)
    {w : Vertices A n} (hw : w ∈ (subdivide (center hA) n (Finsupp.single v 1)).support) (i : Fin (n + 1)) :
    (w i).val ∈ convexHull ℝ (Set.range (fun j => (v j).val)) := by
  have hc := subdivide_mem_convex_carrier hA (convex_convexHull ℝ _) n
    (single_mem_carried {x : A | x.val ∈ convexHull ℝ (Set.range (fun j => (v j).val))} v 1
      (fun j => subset_convexHull ℝ _ ⟨j, rfl⟩))
  exact hc hw i

theorem homotopy_vertices_mem_convexHull {n : ℕ} (v : Vertices A n)
    {w : Vertices A (n + 1)}
    (hw : w ∈ (subdivideHomotopy (center hA) n (Finsupp.single v 1)).support) (i : Fin (n + 2)) :
    (w i).val ∈ convexHull ℝ (Set.range (fun j => (v j).val)) := by
  have hc := homotopy_mem_convex_carrier hA (convex_convexHull ℝ _) n
    (single_mem_carried {x : A | x.val ∈ convexHull ℝ (Set.range (fun j => (v j).val))} v 1
      (fun j => subset_convexHull ℝ _ ⟨j, rfl⟩))
  exact hc hw i

noncomputable def shrink (n : ℕ) : ℝ := (n : ℝ) / (n + 1)

theorem shrink_nonneg (n : ℕ) : 0 ≤ shrink n := by unfold shrink; positivity

theorem shrink_lt_one (n : ℕ) : shrink n < 1 := by
  unfold shrink
  exact (div_lt_one (by positivity)).mpr (by linarith)

theorem center_dist_vertex_le {n : ℕ} (v : Vertices A n) (D : ℝ)
    (hD : ∀ i j, dist (v i).val (v j).val ≤ D) (j : Fin (n + 1)) :
    dist (center hA n v).val (v j).val ≤ shrink n * D := by
  classical
  let a : ℝ := ((n + 1 : ℕ) : ℝ)⁻¹
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hsum : ∑ i : Fin (n + 1), a = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, a]
    exact mul_inv_cancel₀ (by positivity)
  have hv : (center hA n v).val - (v j).val = ∑ i, a • ((v i).val - (v j).val) := by
    rw [center_val]
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul]
    rfl
  have hd : (∑ i : Fin (n + 1), dist (v i).val (v j).val) ≤ (n : ℝ) * D := by
    calc
      _ = ∑ i ∈ Finset.univ.erase j, dist (v i).val (v j).val := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), dist_self, add_zero]
      _ ≤ ∑ _i ∈ Finset.univ.erase j, D := Finset.sum_le_sum (fun i _ => hD i j)
      _ = _ := by simp
  rw [dist_eq_norm, hv]
  calc
    _ ≤ ∑ i, ‖a • ((v i).val - (v j).val)‖ := norm_sum_le _ _
    _ = a * ∑ i, dist (v i).val (v j).val := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, ← dist_eq_norm, Finset.mul_sum]
    _ ≤ a * ((n : ℝ) * D) := mul_le_mul_of_nonneg_left hd ha
    _ = shrink n * D := by simp only [a, shrink, Nat.cast_add, Nat.cast_one, div_eq_mul_inv]; ring

theorem center_dist_convexHull_le {n : ℕ} (v : Vertices A n) (D : ℝ)
    (hD : ∀ i j, dist (v i).val (v j).val ≤ D) {x : E}
    (hx : x ∈ convexHull ℝ (Set.range (fun j => (v j).val))) :
    dist (center hA n v).val x ≤ shrink n * D := by
  obtain ⟨y, ⟨j, rfl⟩, hj⟩ := convexHull_exists_dist_ge hx (center hA n v).val
  rw [dist_comm] at hj
  exact hj.trans (by simpa only [dist_comm] using center_dist_vertex_le hA v D hD j)

theorem affineEval_dist_le {n : ℕ} (v : Vertices A n) (D : ℝ)
    (hD : ∀ i j, dist (v i).val (v j).val ≤ D) (z w : TopologicalSingular.Domain n) :
    dist (affineEval hA v z).val (affineEval hA v w).val ≤ D := by
  have hm (t : TopologicalSingular.Domain n) :
      (affineEval hA v t).val ∈ convexHull ℝ (Set.range (fun j => (v j).val)) :=
    affineEval_mem_of_vertices hA (convex_convexHull ℝ (Set.range (fun j => (v j).val))) v
      (fun j => subset_convexHull ℝ _ ⟨j, rfl⟩) t
  obtain ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, hij⟩ := convexHull_exists_dist_ge2 (hm z) (hm w)
  exact hij.trans (hD i j)

end FiniteChains.AffineVertexChains
