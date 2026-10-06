module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.PrismGeometry
public import RequestProject.TopologicalSingular.PrismCancellation

@[expose] public section

/-! # The singular prism identity for actual continuous homotopies -/


namespace FiniteChains.SingularPrism

open Set Topology TopologicalSingular

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)

noncomputable def prism (n : ℕ) : Chain X n →ₗ[ℤ] Chain Y (n + 1) :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • Finsupp.lmapDomain ℤ ℤ (fun σ => simplex H σ i)

theorem prism_single (n : ℕ) (σ : Simplex X n) (r : ℤ) :
    prism H n (Finsupp.single σ r) = altSum (fun i => Finsupp.single (simplex H σ i) r) := by
  simp only [prism, LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, altSum]

theorem boundary_prism_single (n : ℕ) (σ : Simplex X n) (r : ℤ) :
    boundary n (prism H n (Finsupp.single σ r)) =
      altSum (fun i => altSum (fun j => Finsupp.single (face j (simplex H σ i)) r)) := by
  simp only [prism_single, altSum, map_sum, map_zsmul, boundary_single]

theorem prism_boundary_single (n : ℕ) (σ : Simplex X (n + 1)) (r : ℤ) :
    prism H n (boundary n (Finsupp.single σ r)) =
      altSum (fun j => altSum (fun i => Finsupp.single (simplex H (face j σ) i) r)) := by
  simp only [boundary_single, map_sum, map_zsmul, prism_single, altSum]

theorem prism_identity_zero_single (σ : Simplex X 0) (r : ℤ) :
    boundary 0 (prism H 0 (Finsupp.single σ r)) =
      TopologicalSingular.map g 0 (Finsupp.single σ r) - TopologicalSingular.map f 0 (Finsupp.single σ r) := by
  let A : Fin 1 → Fin 2 → Chain Y 0 := fun i j => Finsupp.single (face j (simplex H σ i)) r
  have hh := prism_cancellation 0 A (fun i => Fin.elim0 i)
  have hz : altSum (fun i : Fin 0 => altSum (side A i)) = 0 := by simp [altSum]
  rw [hz, add_zero] at hh
  rw [boundary_prism_single, TopologicalSingular.map_single, TopologicalSingular.map_single]
  simpa only [A, simplex_first, simplex_last] using hh

theorem prism_identity_succ_single (n : ℕ) (σ : Simplex X (n + 1)) (r : ℤ) :
    boundary (n + 1) (prism H (n + 1) (Finsupp.single σ r)) +
      prism H n (boundary n (Finsupp.single σ r)) =
      TopologicalSingular.map g (n + 1) (Finsupp.single σ r) -
        TopologicalSingular.map f (n + 1) (Finsupp.single σ r) := by
  let A : Fin (n + 2) → Fin (n + 3) → Chain Y (n + 1) :=
    fun i j => Finsupp.single (face j (simplex H σ i)) r
  have hd : ∀ i : Fin (n + 1), A i.castSucc i.succ.castSucc = A i.succ i.succ.castSucc := by
    intro i
    exact congrArg (fun τ => Finsupp.single τ r) (simplex_middle H σ i)
  have hh := prism_cancellation (n + 1) A hd
  have hs : side A = fun i j => Finsupp.single (simplex H (face j σ) i) r := by
    funext i j
    unfold side
    split_ifs with hij
    · exact congrArg (fun τ => Finsupp.single τ r) (simplex_left H σ i j hij)
    · exact congrArg (fun τ => Finsupp.single τ r) (simplex_right H σ i j (lt_of_not_ge hij))
  rw [hs, altSum_comm (fun i j => Finsupp.single (simplex H (face j σ) i) r)] at hh
  rw [boundary_prism_single, prism_boundary_single, TopologicalSingular.map_single, TopologicalSingular.map_single]
  simpa only [A, simplex_first, simplex_last] using hh

theorem prism_identity_zero (c : Chain X 0) :
    boundary 0 (prism H 0 c) = TopologicalSingular.map g 0 c - TopologicalSingular.map f 0 c := by
  have he : (boundary 0).comp (prism H 0) = TopologicalSingular.map g 0 - TopologicalSingular.map f 0 := by
    apply Finsupp.lhom_ext
    exact prism_identity_zero_single H
  exact DFunLike.congr_fun he c

theorem prism_identity_succ (n : ℕ) (c : Chain X (n + 1)) :
    boundary (n + 1) (prism H (n + 1) c) + prism H n (boundary n c) =
      TopologicalSingular.map g (n + 1) c - TopologicalSingular.map f (n + 1) c := by
  have he : (boundary (n + 1)).comp (prism H (n + 1)) + (prism H n).comp (boundary n) =
      TopologicalSingular.map g (n + 1) - TopologicalSingular.map f (n + 1) := by
    apply Finsupp.lhom_ext
    exact prism_identity_succ_single H n
  exact DFunLike.congr_fun he c

include H in
theorem homotopic_maps_difference_bounds_zero (c : Chain X 0) :
    TopologicalSingular.map g 0 c - TopologicalSingular.map f 0 c ∈ LinearMap.range (boundary 0) :=
  ⟨prism H 0 c, prism_identity_zero H c⟩

include H in
theorem homotopic_maps_difference_bounds (n : ℕ) (c : Chain X (n + 1)) (hc : boundary n c = 0) :
    TopologicalSingular.map g (n + 1) c - TopologicalSingular.map f (n + 1) c ∈
      LinearMap.range (boundary (n + 1)) := by
  refine ⟨prism H (n + 1) c, ?_⟩
  simpa only [hc, map_zero, add_zero] using prism_identity_succ H n c

end FiniteChains.SingularPrism
