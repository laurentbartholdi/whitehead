/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.VertexSubdivisionHomotopy
import Mathlib.LinearAlgebra.Finsupp.Supported

/-! # Carrier control for subdivision and its homotopy -/


namespace FiniteChains.VertexChains

universe u
variable {V : Type u}

theorem map_mem_of_supported {ι M : Type*} [AddCommGroup M] [Module ℤ M]
    (S : Set ι) (T : Submodule ℤ M) (L : (ι →₀ ℤ) →ₗ[ℤ] M)
    (hL : ∀ v ∈ S, L (Finsupp.single v 1) ∈ T)
    {c : ι →₀ ℤ} (hc : c ∈ Finsupp.supported ℤ ℤ S) : L c ∈ T := by
  have he : Finsupp.supported ℤ ℤ S ≤ T.comap L := by
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    exact hL v hv
  exact he hc

noncomputable def carried (S : Set V) (n : ℕ) : Submodule ℤ (Chain V n) :=
  Finsupp.supported ℤ ℤ {v | ∀ i, v i ∈ S}

theorem single_mem_carried (S : Set V) {n : ℕ} (v : Vertices V n) (r : ℤ) (hv : ∀ i, v i ∈ S) :
    Finsupp.single v r ∈ carried S n := Finsupp.single_mem_supported ℤ r hv

theorem boundary_mem_carried (S : Set V) (n : ℕ) {c : Chain V (n + 1)}
    (hc : c ∈ carried S (n + 1)) : boundary n c ∈ carried S n := by
  apply map_mem_of_supported _ _ (boundary n) ?_ hc
  intro v hv
  rw [boundary_single]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact single_mem_carried S _ 1 (fun j => hv (i.succAbove j))

theorem cone_mem_carried (S : Set V) (p : V) (hp : p ∈ S) (n : ℕ) {c : Chain V n}
    (hc : c ∈ carried S n) : cone p n c ∈ carried S (n + 1) := by
  apply map_mem_of_supported _ _ (cone p n) ?_ hc
  intro v hv
  rw [cone_single]
  apply single_mem_carried
  intro i
  exact Fin.cases hp (fun j => hv j) i

variable (center : ∀ n, Vertices V n → V) (S : Set V)
variable (hcenter : ∀ n v, (∀ i, v i ∈ S) → center n v ∈ S)

include hcenter in
theorem subdivide_mem_carried (n : ℕ) {c : Chain V n} (hc : c ∈ carried S n) :
    subdivide center n c ∈ carried S n := by
  induction n with
  | zero => exact hc
  | succ n ih =>
    apply map_mem_of_supported _ _ (subdivide center (n + 1)) ?_ hc
    intro v hv
    rw [subdivide_succ_single, one_smul]
    apply cone_mem_carried S _ (hcenter _ _ hv)
    apply ih
    exact boundary_mem_carried S n (single_mem_carried S v 1 hv)

include hcenter in
theorem subdivideHomotopy_mem_carried (n : ℕ) {c : Chain V n} (hc : c ∈ carried S n) :
    subdivideHomotopy center n c ∈ carried S (n + 1) := by
  induction n with
  | zero => rw [subdivideHomotopy_zero]; exact Submodule.zero_mem _
  | succ n ih =>
    apply map_mem_of_supported _ _ (subdivideHomotopy center (n + 1)) ?_ hc
    intro v hv
    rw [subdivideHomotopy_succ_single, one_smul]
    apply cone_mem_carried S _ (hv 0)
    apply Submodule.sub_mem
    · exact Submodule.sub_mem _
        (subdivide_mem_carried center S hcenter (n + 1) (single_mem_carried S v 1 hv))
        (single_mem_carried S v 1 hv)
    · exact ih (boundary_mem_carried S n (single_mem_carried S v 1 hv))

end FiniteChains.VertexChains
