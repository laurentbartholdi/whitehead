module

public import Mathlib

@[expose] public section

/-!
# Generation over the group ring from a transitive deck action

Step 3 of Lemma 3.6 (the generation lemma behind property (B2) of the blocks) reads:

> Cellular quotient chains give `H₂(W̃, U) ≅ H₂(V, V₀) = H₂(V) = 0`.  Hence
> `H₂(U) → H₂(W̃)` is surjective.  The deck group permutes the components of `U`
> transitively.  Hurewicz now gives exactly the asserted generation of `π₂(W)`.

The same two-step pattern — "surjective, and the deck group permutes the pieces
transitively, hence generated over the group ring by one piece" — is used again in
Proposition 3.11.  This file proves that pattern.

* `FiniteChains.span_of_transitive_components` — a module over a group ring which is the sum
  of a family of subgroups permuted transitively by the group is generated, over the group
  ring, by any one of them;
* `FiniteChains.span_image_eq_top` — a surjection carries a generating set to a generating
  set;
* `FiniteChains.generation_of_surjective_of_transitive` — the two combined, in the form used
  in the paper: `π₂(W)` is generated over `ℤ[π₁(W)]` by the image of `π₂(X)`.
-/

namespace FiniteChains

open MonoidAlgebra

section Transitive

variable {Λ : Type*} [Group Λ] {M : Type*} [AddCommGroup M]
  [Module (MonoidAlgebra ℤ Λ) M] {ι : Type*}

/-- **The deck group permutes the components transitively, so one component generates.**
`A i` are the second homologies of the components of the inverse image `U`, sitting inside
the module `M = H₂(U)`; the hypothesis `hsum` says that every element of `M` is a finite sum
of elements of the components (a cycle has finite support), and `htrans` says that every
component is a deck translate of the chosen one. -/
theorem span_of_transitive_components (A : ι → AddSubgroup M) (i₀ : ι)
    (hsum : ∀ m : M, ∃ (s : Finset ι) (f : ι → M), (∀ i ∈ s, f i ∈ A i) ∧ m = ∑ i ∈ s, f i)
    (htrans : ∀ i : ι, ∃ g : Λ, ∀ x ∈ A i, ∃ y ∈ A i₀,
      x = (MonoidAlgebra.single g (1 : ℤ) : MonoidAlgebra ℤ Λ) • y) :
    Submodule.span (MonoidAlgebra ℤ Λ) (A i₀ : Set M) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun m => ?_
  obtain ⟨s, f, hf, rfl⟩ := hsum m
  refine Submodule.sum_mem _ fun i hi => ?_
  obtain ⟨g, hg⟩ := htrans i
  obtain ⟨y, hy, hxy⟩ := hg (f i) (hf i hi)
  rw [hxy]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hy)

variable {N : Type*} [AddCommGroup N] [Module (MonoidAlgebra ℤ Λ) N]

/-- A surjection of modules carries a generating set to a generating set. -/
theorem span_image_eq_top (f : M →ₗ[MonoidAlgebra ℤ Λ] N) (hf : Function.Surjective f)
    (S : Set M) (hS : Submodule.span (MonoidAlgebra ℤ Λ) S = ⊤) :
    Submodule.span (MonoidAlgebra ℤ Λ) (f '' S) = ⊤ := by
  rw [← Submodule.map_span, hS, Submodule.map_top, LinearMap.range_eq_top.2 hf]

/-- **The generation statement of Lemma 3.6 (and of Proposition 3.11).**  If the second
homology of the inverse image `U` surjects onto that of the universal cover, and the deck
group permutes the components of `U` transitively, then the target is generated, over the
group ring, by the image of the chosen component — that is, by the image of `π₂(X)`. -/
theorem generation_of_surjective_of_transitive (A : ι → AddSubgroup M) (i₀ : ι)
    (hsum : ∀ m : M, ∃ (s : Finset ι) (f : ι → M), (∀ i ∈ s, f i ∈ A i) ∧ m = ∑ i ∈ s, f i)
    (htrans : ∀ i : ι, ∃ g : Λ, ∀ x ∈ A i, ∃ y ∈ A i₀,
      x = (MonoidAlgebra.single g (1 : ℤ) : MonoidAlgebra ℤ Λ) • y)
    (f : M →ₗ[MonoidAlgebra ℤ Λ] N) (hf : Function.Surjective f) :
    Submodule.span (MonoidAlgebra ℤ Λ) (f '' (A i₀ : Set M)) = ⊤ :=
  span_image_eq_top f hf _ (span_of_transitive_components A i₀ hsum htrans)

end Transitive

end FiniteChains
