module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.SubdivisionRealization
public import RequestProject.TopologicalSingular.BarycentricMesh
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Module.LinearMap.End

@[expose] public section

/-! # Sufficient subdivision makes every singular chain small

Small means that every simplex in the support is contained in one member
of the given cover. Compactness of the standard simplex and the proved
mesh estimate supply a finite subdivision exponent. No excision premise
is introduced.
-/


namespace FiniteChains.SingularSubdivision

open Set Topology TopologicalSingular AffineVertexChains

universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}

noncomputable def smallChains (U : ι → Set X) (n : ℕ) : Submodule ℤ (Chain X n) :=
  Finsupp.supported ℤ ℤ {σ | ∃ i, ∀ z, σ z ∈ U i}

theorem single_mem_small (U : ι → Set X) (n : ℕ) (σ : Simplex X n) (r : ℤ)
    (hσ : ∃ i, ∀ z, σ z ∈ U i) : Finsupp.single σ r ∈ smallChains U n :=
  Finsupp.single_mem_supported ℤ r hσ

theorem boundary_mem_small (U : ι → Set X) (n : ℕ) {c : Chain X (n + 1)}
    (hc : c ∈ smallChains U (n + 1)) : boundary n c ∈ smallChains U n := by
  apply VertexChains.map_mem_of_supported _ _ (boundary n) ?_ hc
  rintro σ ⟨j, hj⟩
  rw [boundary_single]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact single_mem_small U n _ 1 ⟨j, fun z => hj _⟩

theorem push_mem_small (U : ι → Set X) {k : ℕ} (σ : Simplex X k)
    (hσ : ∃ i, ∀ z, σ z ∈ U i) (l : ℕ) (c : Chain (Domain k) l) :
    TopologicalSingular.map σ l c ∈ smallChains U l := by
  obtain ⟨j, hj⟩ := hσ
  induction c using Finsupp.induction with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | single_add τ r c _ _ ih =>
    rw [map_add, map_single]
    exact Submodule.add_mem _ (single_mem_small U l _ r ⟨j, fun z => hj (τ z)⟩) ih

theorem fromModel_mem_small (U : ι → Set X) {k l : ℕ} (m : Chain (Domain k) l)
    {c : Chain X k} (hc : c ∈ smallChains U k) : fromModel m c ∈ smallChains U l := by
  apply VertexChains.map_mem_of_supported _ _ (fromModel m) ?_ hc
  intro σ hσ
  rw [fromModel_single, one_smul]
  exact push_mem_small U σ hσ l m

theorem subdivide_mem_small (U : ι → Set X) (n : ℕ) {c : Chain X n}
    (hc : c ∈ smallChains U n) : subdivide n c ∈ smallChains U n :=
  fromModel_mem_small U (model n) hc

theorem homotopy_mem_small (U : ι → Set X) (n : ℕ) {c : Chain X n}
    (hc : c ∈ smallChains U n) : homotopy n c ∈ smallChains U (n + 1) :=
  fromModel_mem_small U (homotopyModel n) hc

theorem iterated_subdivide_mem_small (U : ι → Set X) (k n : ℕ) {c : Chain X n}
    (hc : c ∈ smallChains U n) : ((subdivide n)^[k]) c ∈ smallChains U n := by
  induction k with
  | zero => exact hc
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact subdivide_mem_small U n ih

theorem iterated_subdivide_small_of_le (U : ι → Set X) {k l : ℕ} (hkl : k ≤ l)
    (n : ℕ) {c : Chain X n} (hc : ((subdivide n)^[k]) c ∈ smallChains U n) :
    ((subdivide n)^[l]) c ∈ smallChains U n := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hkl
  rw [Nat.add_comm k a, Function.iterate_add_apply]
  exact iterated_subdivide_mem_small U a n hc

theorem standardVertices_mesh (n : ℕ) : MeshBound (standardVertices n) 1 := by
  intro i j
  exact (Metric.dist_le_diam_of_mem (bounded_stdSimplex (Fin (n + 1)))
    (standardVertices n i).property (standardVertices n j).property).trans diam_stdSimplex_le

theorem exists_subdivision_small_single (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (n : ℕ) (σ : Simplex X n) (hcover : ∀ z, ∃ i, σ z ∈ U i) :
    ∃ k, ((subdivide n)^[k]) (Finsupp.single σ 1) ∈ smallChains U n := by
  classical
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    (isCompact_univ : IsCompact (Set.univ : Set (Domain n)))
    (fun i => (hU i).preimage σ.continuous)
    (by
      intro z _
      obtain ⟨i, hi⟩ := hcover z
      exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ (shrink_lt_one n)
  refine ⟨k, ?_⟩
  rw [iterated_subdivide_single_model]
  apply VertexChains.map_mem_of_supported {v | MeshBound v ((shrink n) ^ k * 1)} (smallChains U n)
    ((TopologicalSingular.map σ n).comp (realize (convex_stdSimplex ℝ (Fin (n + 1))) n)) ?_ ?_
  · intro v hv
    rw [LinearMap.comp_apply, realize_single, map_single]
    obtain ⟨i, hi⟩ := hball (affineEval (convex_stdSimplex ℝ (Fin (n + 1))) v (stdSimplex.vertex 0))
      (Set.mem_univ _)
    apply single_mem_small
    refine ⟨i, fun z => hi ?_⟩
    change dist (affineEval (convex_stdSimplex ℝ (Fin (n + 1))) v z)
      (affineEval (convex_stdSimplex ℝ (Fin (n + 1))) v (stdSimplex.vertex 0)) < δ
    exact (affineEval_dist_le _ v _ hv z (stdSimplex.vertex 0)).trans_lt (by simpa using hk)
  · exact iterated_subdivide_mem_mesh (convex_stdSimplex ℝ (Fin (n + 1))) k n 1 zero_le_one
      (Finsupp.single_mem_supported ℤ 1 (standardVertices_mesh n))

theorem exists_subdivision_small (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) (c : Chain X n) :
    ∃ k, ((subdivide n)^[k]) c ∈ smallChains U n := by
  classical
  choose K hK using fun σ : Simplex X n => exists_subdivision_small_single U hU n σ (fun z => hcover (σ z))
  let N := c.support.sup K
  refine ⟨N, ?_⟩
  rw [← Module.End.pow_apply]
  apply VertexChains.map_mem_of_supported (c.support : Set (Simplex X n)) (smallChains U n)
    ((subdivide n) ^ N) ?_ (fun _ h => h)
  intro σ hσ
  rw [Module.End.pow_apply]
  exact iterated_subdivide_small_of_le U (Finset.le_sup hσ) n (hK σ)

end FiniteChains.SingularSubdivision
