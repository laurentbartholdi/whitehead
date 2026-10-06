/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.SmallSingularChains

/-! # Small representatives and small fillings of singular cycles

For an open cover, every cycle is homologous to a small cycle. A small
cycle bounding in the ambient singular complex already bounds by a small
chain. The accumulated subdivision homotopy is explicit.
-/


namespace FiniteChains.SingularSubdivision

open Set Topology TopologicalSingular

universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}

theorem iterated_subdivide_zero (k n : ℕ) : ((subdivide (X := X) n)^[k]) 0 = 0 := by
  rw [← Module.End.pow_apply, map_zero]

theorem iterated_subdivide_boundary (k n : ℕ) (c : Chain X (n + 1)) :
    ((subdivide n)^[k]) (boundary n c) = boundary n (((subdivide (n + 1))^[k]) c) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, subdivide_boundary]

noncomputable def iteratedHomotopy (n : ℕ) : ℕ → Chain X n →ₗ[ℤ] Chain X (n + 1)
  | 0 => 0
  | k + 1 => (homotopy n).comp ((subdivide n) ^ k) + iteratedHomotopy n k

theorem iteratedHomotopy_zero (n : ℕ) (c : Chain X n) : iteratedHomotopy n 0 c = 0 := rfl

theorem iteratedHomotopy_succ (n k : ℕ) (c : Chain X n) :
    iteratedHomotopy n (k + 1) c = homotopy n (((subdivide n)^[k]) c) + iteratedHomotopy n k c := by
  simp only [iteratedHomotopy, LinearMap.add_apply, LinearMap.comp_apply, Module.End.pow_apply]

theorem iteratedHomotopy_identity_zero (k : ℕ) (c : Chain X 0) :
    boundary 0 (iteratedHomotopy 0 k c) = ((subdivide 0)^[k]) c - c := by
  induction k with
  | zero => simp only [iteratedHomotopy_zero, map_zero, Function.iterate_zero_apply, sub_self]
  | succ k ih =>
    rw [iteratedHomotopy_succ, map_add, homotopy_identity_zero, ih, Function.iterate_succ_apply']
    abel

theorem iteratedHomotopy_identity_succ (k n : ℕ) (c : Chain X (n + 1)) :
    boundary (n + 1) (iteratedHomotopy (n + 1) k c) + iteratedHomotopy n k (boundary n c) =
      ((subdivide (n + 1))^[k]) c - c := by
  induction k with
  | zero => simp only [iteratedHomotopy_zero, map_zero, add_zero, Function.iterate_zero_apply, sub_self]
  | succ k ih =>
    rw [iteratedHomotopy_succ, iteratedHomotopy_succ, map_add, iterated_subdivide_boundary]
    calc
      _ = (boundary (n + 1) (homotopy (n + 1) (((subdivide (n + 1))^[k]) c)) +
            homotopy n (boundary n (((subdivide (n + 1))^[k]) c))) +
          (boundary (n + 1) (iteratedHomotopy (n + 1) k c) +
            iteratedHomotopy n k (boundary n c)) := by abel
      _ = (subdivide (n + 1) (((subdivide (n + 1))^[k]) c) - ((subdivide (n + 1))^[k]) c) +
          (((subdivide (n + 1))^[k]) c - c) := by rw [homotopy_identity_succ, ih]
      _ = _ := by rw [Function.iterate_succ_apply']; abel

theorem iteratedHomotopy_mem_small (U : ι → Set X) (k n : ℕ) {c : Chain X n}
    (hc : c ∈ smallChains U n) : iteratedHomotopy n k c ∈ smallChains U (n + 1) := by
  induction k with
  | zero => rw [iteratedHomotopy_zero]; exact Submodule.zero_mem _
  | succ k ih =>
    rw [iteratedHomotopy_succ]
    exact Submodule.add_mem _ (homotopy_mem_small U n (iterated_subdivide_mem_small U k n hc)) ih

variable (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)

include hU hcover in
theorem exists_small_representative_zero (c : Chain X 0) :
    ∃ d : Chain X 0, d ∈ smallChains U 0 ∧ d - c ∈ LinearMap.range (boundary 0) := by
  obtain ⟨k, hk⟩ := exists_subdivision_small U hU hcover 0 c
  exact ⟨_, hk, iteratedHomotopy 0 k c, iteratedHomotopy_identity_zero k c⟩

include hU hcover in
theorem exists_small_cycle_representative (n : ℕ) (c : Chain X (n + 1)) (hc : boundary n c = 0) :
    ∃ d : Chain X (n + 1), d ∈ smallChains U (n + 1) ∧ boundary n d = 0 ∧
      d - c ∈ LinearMap.range (boundary (n + 1)) := by
  obtain ⟨k, hk⟩ := exists_subdivision_small U hU hcover (n + 1) c
  refine ⟨_, hk, ?_, iteratedHomotopy (n + 1) k c, ?_⟩
  · rw [← iterated_subdivide_boundary, hc, iterated_subdivide_zero]
  · simpa only [hc, map_zero, add_zero] using iteratedHomotopy_identity_succ k n c

include hU hcover in
theorem exists_small_filling_zero (c : Chain X 0) (hc : c ∈ smallChains U 0)
    (b : Chain X 1) (hb : boundary 0 b = c) :
    ∃ a : Chain X 1, a ∈ smallChains U 1 ∧ boundary 0 a = c := by
  obtain ⟨k, hk⟩ := exists_subdivision_small U hU hcover 1 b
  refine ⟨((subdivide 1)^[k]) b - iteratedHomotopy 0 k c,
    Submodule.sub_mem _ hk (iteratedHomotopy_mem_small U k 0 hc), ?_⟩
  rw [map_sub, ← iterated_subdivide_boundary, hb, iteratedHomotopy_identity_zero]
  abel

include hU hcover in
theorem exists_small_filling (n : ℕ) (c : Chain X (n + 1)) (hc : c ∈ smallChains U (n + 1))
    (b : Chain X (n + 2)) (hb : boundary (n + 1) b = c) :
    ∃ a : Chain X (n + 2), a ∈ smallChains U (n + 2) ∧ boundary (n + 1) a = c := by
  obtain ⟨k, hk⟩ := exists_subdivision_small U hU hcover (n + 2) b
  have hz : boundary n c = 0 := by rw [← hb, boundary_boundary]
  have hh := iteratedHomotopy_identity_succ k n c
  rw [hz, map_zero, add_zero] at hh
  refine ⟨((subdivide (n + 2))^[k]) b - iteratedHomotopy (n + 1) k c,
    Submodule.sub_mem _ hk (iteratedHomotopy_mem_small U k (n + 1) hc), ?_⟩
  rw [map_sub, ← iterated_subdivide_boundary, hb, hh]
  abel

end FiniteChains.SingularSubdivision
