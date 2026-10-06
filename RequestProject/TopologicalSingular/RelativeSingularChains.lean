module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.SingularChainMaps
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

/-! # Relative singular chains of an actual topological pair

These are quotients by chains of the subspace, not an assumed cellular
chain complex. The short exact sequence and the relative differential
are constructed directly. No excision or homotopy comparison is assumed.
-/


namespace FiniteChains.TopologicalSingular

open Set Topology

universe u

variable {X : Type u} [TopologicalSpace X]

def inclusion (A : Set X) : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩

theorem simplexMap_inclusion_injective (A : Set X) (n : ℕ) :
    Function.Injective (simplexMap (inclusion A) n) := by
  intro σ τ he
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  exact DFunLike.congr_fun he z

theorem map_inclusion_injective (A : Set X) (n : ℕ) : Function.Injective (map (inclusion A) n) := by
  exact Finsupp.mapDomain_injective (simplexMap_inclusion_injective A n)

noncomputable def subChains (A : Set X) (n : ℕ) : Submodule ℤ (Chain X n) :=
  LinearMap.range (map (inclusion A) n)

theorem boundary_mem_subChains (A : Set X) (n : ℕ) {c : Chain X (n + 1)}
    (hc : c ∈ subChains A (n + 1)) : boundary n c ∈ subChains A n := by
  obtain ⟨b, rfl⟩ := hc
  exact ⟨boundary n b, map_boundary (inclusion A) n b⟩

abbrev RelativeChain (A : Set X) (n : ℕ) := Chain X n ⧸ subChains A n

noncomputable def relativeProjection (A : Set X) (n : ℕ) : Chain X n →ₗ[ℤ] RelativeChain A n :=
  (subChains A n).mkQ

theorem relativeProjection_surjective (A : Set X) (n : ℕ) :
    Function.Surjective (relativeProjection A n) := (subChains A n).mkQ_surjective

theorem ker_relativeProjection (A : Set X) (n : ℕ) :
    LinearMap.ker (relativeProjection A n) = LinearMap.range (map (inclusion A) n) :=
  (subChains A n).ker_mkQ

theorem relativeProjection_eq_zero_iff (A : Set X) (n : ℕ) (c : Chain X n) :
    relativeProjection A n c = 0 ↔ c ∈ subChains A n := by
  change c ∈ LinearMap.ker (relativeProjection A n) ↔ _
  rw [ker_relativeProjection]
  rfl

noncomputable def relativeBoundary (A : Set X) (n : ℕ) : RelativeChain A (n + 1) →ₗ[ℤ] RelativeChain A n :=
  (subChains A (n + 1)).mapQ (subChains A n) (boundary n)
    (fun _ h => boundary_mem_subChains A n h)

theorem relativeBoundary_projection (A : Set X) (n : ℕ) (c : Chain X (n + 1)) :
    relativeBoundary A n (relativeProjection A (n + 1) c) = relativeProjection A n (boundary n c) := rfl

theorem relativeBoundary_squared (A : Set X) (n : ℕ) :
    (relativeBoundary A n).comp (relativeBoundary A (n + 1)) = 0 := by
  apply LinearMap.ext
  intro q
  obtain ⟨c, rfl⟩ := relativeProjection_surjective A (n + 2) q
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, relativeBoundary_projection,
    boundary_boundary, map_zero]

noncomputable def relativeComplex (A : Set X) : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of ℤ (RelativeChain A n))
    (fun n => ModuleCat.ofHom (relativeBoundary A n))
    (fun n => ModuleCat.hom_ext (relativeBoundary_squared A n))

theorem relativeCycle_iff (A : Set X) (n : ℕ) (c : Chain X (n + 1)) :
    relativeBoundary A n (relativeProjection A (n + 1) c) = 0 ↔ boundary n c ∈ subChains A n := by
  rw [relativeBoundary_projection, relativeProjection_eq_zero_iff]

theorem relativeCycle_has_representative (A : Set X) (n : ℕ) (q : RelativeChain A (n + 1))
    (hq : relativeBoundary A n q = 0) :
    ∃ c : Chain X (n + 1), relativeProjection A (n + 1) c = q ∧ boundary n c ∈ subChains A n := by
  obtain ⟨c, rfl⟩ := relativeProjection_surjective A (n + 1) q
  exact ⟨c, rfl, (relativeCycle_iff A n c).mp hq⟩

theorem subChains_mono {A B : Set X} (h : A ⊆ B) (n : ℕ) : subChains A n ≤ subChains B n := by
  let j : C(A, B) := ⟨fun x => ⟨x.val, h x.property⟩, continuous_subtype_val.subtype_mk _⟩
  rintro _ ⟨c, rfl⟩
  refine ⟨map j n c, ?_⟩
  have he : (inclusion B).comp j = inclusion A := rfl
  have hm := DFunLike.congr_fun (map_comp j (inclusion B) n) c
  rw [he] at hm
  exact hm.symm

noncomputable def relativeTransition {A B : Set X} (h : A ⊆ B) (n : ℕ) :
    RelativeChain A n →ₗ[ℤ] RelativeChain B n :=
  (subChains A n).mapQ (subChains B n) LinearMap.id (subChains_mono h n)

theorem relativeTransition_projection {A B : Set X} (h : A ⊆ B) (n : ℕ) (c : Chain X n) :
    relativeTransition h n (relativeProjection A n c) = relativeProjection B n c := rfl

theorem relativeTransition_boundary {A B : Set X} (h : A ⊆ B) (n : ℕ) (q : RelativeChain A (n + 1)) :
    relativeTransition h n (relativeBoundary A n q) =
      relativeBoundary B n (relativeTransition h (n + 1) q) := by
  obtain ⟨c, rfl⟩ := relativeProjection_surjective A (n + 1) q
  rfl

end FiniteChains.TopologicalSingular
