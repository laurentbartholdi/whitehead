/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.SingularPrism
import RequestProject.TopologicalSingular.RelativeSingularMaps

/-! # The prism identity for homotopies of topological pairs -/


namespace FiniteChains.SingularPrism

open Set Topology TopologicalSingular

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)
variable (A : Set X) (B : Set Y) (hH : ∀ t : unitInterval, ∀ x ∈ A, H (t, x) ∈ B)

include H hH in
theorem homotopy_zero_mapsTo : MapsTo f A B := by
  intro x hx
  rw [← H.apply_zero x]
  exact hH 0 x hx

include H hH in
theorem homotopy_one_mapsTo : MapsTo g A B := by
  intro x hx
  rw [← H.apply_one x]
  exact hH 1 x hx

include hH in
theorem prism_single_mem_subChains (n : ℕ) (σ : Simplex X n) (r : ℤ) (hσ : ∀ z, σ z ∈ A) :
    prism H n (Finsupp.single σ r) ∈ subChains B (n + 1) := by
  rw [prism_single, altSum]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  apply single_mem_subChains
  intro z
  exact hH _ _ (hσ _)

include hH in
theorem prism_mem_subChains (n : ℕ) {c : Chain X n} (hc : c ∈ subChains A n) :
    prism H n c ∈ subChains B (n + 1) := by
  obtain ⟨b, rfl⟩ := hc
  induction b using Finsupp.induction with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | single_add σ r b _ _ ih =>
    rw [map_add, map_add]
    apply Submodule.add_mem _ _ ih
    rw [TopologicalSingular.map_single]
    exact prism_single_mem_subChains H A B hH n _ r (fun z => (σ z).property)

noncomputable def relativePrism (n : ℕ) : RelativeChain A n →ₗ[ℤ] RelativeChain B (n + 1) :=
  (subChains A n).mapQ (subChains B (n + 1)) (prism H n)
    (fun _ hc => prism_mem_subChains H A B hH n hc)

theorem relativePrism_projection (n : ℕ) (c : Chain X n) :
    relativePrism H A B hH n (relativeProjection A n c) =
      relativeProjection B (n + 1) (prism H n c) := rfl

theorem relativePrism_identity_zero (c : RelativeChain A 0) :
    relativeBoundary B 0 (relativePrism H A B hH 0 c) =
      relativeMap g A B (homotopy_one_mapsTo H A B hH) 0 c -
        relativeMap f A B (homotopy_zero_mapsTo H A B hH) 0 c := by
  obtain ⟨b, rfl⟩ := relativeProjection_surjective A 0 c
  simp only [relativePrism_projection, relativeBoundary_projection, relativeMap_projection,
    prism_identity_zero, map_sub]

theorem relativePrism_identity_succ (n : ℕ) (c : RelativeChain A (n + 1)) :
    relativeBoundary B (n + 1) (relativePrism H A B hH (n + 1) c) +
      relativePrism H A B hH n (relativeBoundary A n c) =
      relativeMap g A B (homotopy_one_mapsTo H A B hH) (n + 1) c -
        relativeMap f A B (homotopy_zero_mapsTo H A B hH) (n + 1) c := by
  obtain ⟨b, rfl⟩ := relativeProjection_surjective A (n + 1) c
  simp only [relativePrism_projection, relativeBoundary_projection, relativeMap_projection]
  rw [← map_add, prism_identity_succ, map_sub]

theorem relative_homotopic_difference_bounds (n : ℕ) (c : RelativeChain A (n + 1))
    (hc : relativeBoundary A n c = 0) :
    relativeMap g A B (homotopy_one_mapsTo H A B hH) (n + 1) c -
      relativeMap f A B (homotopy_zero_mapsTo H A B hH) (n + 1) c ∈
        LinearMap.range (relativeBoundary B (n + 1)) := by
  refine ⟨relativePrism H A B hH (n + 1) c, ?_⟩
  simpa only [hc, map_zero, add_zero] using relativePrism_identity_succ H A B hH n c

end FiniteChains.SingularPrism
