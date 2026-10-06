module

public import RequestProject.TransitiveGeneration

@[expose] public section

/-!
# Step 2–3 of Lemma 3.6: from `H₂(W̃, U) = 0` to generation of `π₂(W)`

Steps 2 and 3 of the proof of the generation lemma of the paper read:

> In `W̃` let `U` be the full inverse image of `X`.  Collapsing each component of `U`
> produces a space `V` with a set of new vertices `V₀`; cellular quotient chains give
> `H₂(W̃, U) ≅ H₂(V, V₀) = H₂(V) = 0`.  Hence `H₂(U) → H₂(W̃)` is surjective.  The deck group
> permutes the components of `U` transitively.  Hurewicz now gives exactly the asserted
> generation of `π₂(W)`.

This file proves the homological algebra of those two steps, over an arbitrary ring `R`
(in the application `R = ℤ[π₁(W)]`, and all chain groups are the equivariant cellular chain
groups of `W̃`, of the invariant subcomplex `U` and of the quotient `C_*(W̃)/C_*(U)`).

* `FiniteChains.h2_surjective_of_relative_vanishing` — the long exact sequence in the only
  form used: if every two-cycle of the quotient complex bounds, then every two-cycle of the
  total complex is a cycle of the subcomplex plus a boundary;
* `FiniteChains.cycles_eq_image_of_relative_vanishing` — the same statement when the total
  complex has no three-cells (the situation after the polygon-cylinder cell has been
  cancelled): then every two-cycle of the total complex is literally the image of a
  two-cycle of the subcomplex;
* `FiniteChains.h2_quotient_vanishing_of_h2_vanishing` — the identification
  `H₂(V, V₀) = H₂(V)`: collapsing a subcomplex concentrated in degree zero does not change
  two-cycles or three-chains, so the vanishing of `H₂(V)` gives the vanishing of the
  relative group;
* `FiniteChains.cycles_mem_span_image_of_relative_vanishing` — the span form: a spanning set
  of the two-cycles of the subcomplex spans the two-cycles of the total complex;
* `FiniteChains.generation_of_relative_vanishing` — the conclusion of step 3: together with
  the transitive permutation of the components of `U` by the deck group
  (`FiniteChains.span_of_transitive_components`), the two-cycles of `W̃` are generated over
  `R = ℤ[π₁(W)]` by the two-cycles of the chosen component, i.e. by the image of `π₂(X)`.

The geometric input that is *not* proved here is `H₂(V) = 0` itself, i.e. the cubical
curvature criterion for the collapsed space `V`.
-/

namespace FiniteChains

section RelativeH2

variable {R : Type*} [Ring R]
variable {A₂ A₁ B₃ B₂ B₁ Q₃ Q₂ Q₁ : Type*}
  [AddCommGroup A₂] [Module R A₂] [AddCommGroup A₁] [Module R A₁]
  [AddCommGroup B₃] [Module R B₃] [AddCommGroup B₂] [Module R B₂]
  [AddCommGroup B₁] [Module R B₁]
  [AddCommGroup Q₃] [Module R Q₃] [AddCommGroup Q₂] [Module R Q₂]
  [AddCommGroup Q₁] [Module R Q₁]

/-- **`H₂(W̃, U) = 0` makes `H₂(U) → H₂(W̃)` surjective.**

The data is the relevant part of a short exact sequence of chain complexes

  `A_* --f--> B_* --g--> Q_*`

in degrees `1, 2, 3` (`A = C_*(U)`, `B = C_*(W̃)`, `Q` the relative complex).  Used are: `g`
is surjective in degree three, the sequence is exact at `B₂`, `f` is injective in degree
one, `f` and `g` are chain maps, and every two-cycle of `Q` bounds (this is
`H₂(W̃, U) = 0`).  The conclusion is that an arbitrary two-cycle of `B` differs from the
image of a two-cycle of `A` by a boundary. -/
theorem h2_surjective_of_relative_vanishing
    (dA₂ : A₂ →ₗ[R] A₁) (dB₃ : B₃ →ₗ[R] B₂) (dB₂ : B₂ →ₗ[R] B₁)
    (dQ₃ : Q₃ →ₗ[R] Q₂) (dQ₂ : Q₂ →ₗ[R] Q₁)
    (f₂ : A₂ →ₗ[R] B₂) (f₁ : A₁ →ₗ[R] B₁)
    (g₃ : B₃ →ₗ[R] Q₃) (g₂ : B₂ →ₗ[R] Q₂) (g₁ : B₁ →ₗ[R] Q₁)
    (hf₁ : Function.Injective f₁)
    (hexB₂ : ∀ b : B₂, g₂ b = 0 → ∃ a : A₂, f₂ a = b)
    (hg₃ : Function.Surjective g₃)
    (hchainF₂ : ∀ a : A₂, dB₂ (f₂ a) = f₁ (dA₂ a))
    (hchainG₃ : ∀ y : B₃, g₂ (dB₃ y) = dQ₃ (g₃ y))
    (hchainG₂ : ∀ b : B₂, g₁ (dB₂ b) = dQ₂ (g₂ b))
    (hdB : ∀ y : B₃, dB₂ (dB₃ y) = 0)
    (hQ : ∀ q : Q₂, dQ₂ q = 0 → ∃ q₃ : Q₃, dQ₃ q₃ = q)
    (z : B₂) (hz : dB₂ z = 0) :
    ∃ (a : A₂) (y : B₃), dA₂ a = 0 ∧ z = f₂ a + dB₃ y := by
  -- the image of `z` in the relative complex is a two-cycle, hence a boundary
  have hcyc : dQ₂ (g₂ z) = 0 := by rw [← hchainG₂ z, hz, map_zero]
  obtain ⟨q₃, hq₃⟩ := hQ _ hcyc
  obtain ⟨y, hy⟩ := hg₃ q₃
  -- correct `z` by that boundary; the result comes from the subcomplex
  have hz' : g₂ (z - dB₃ y) = 0 := by
    rw [map_sub, hchainG₃ y, hy, hq₃, sub_self]
  obtain ⟨a, ha⟩ := hexB₂ _ hz'
  refine ⟨a, y, ?_, ?_⟩
  · refine hf₁ ?_
    rw [map_zero, ← hchainF₂ a, ha, map_sub, hz, hdB y, sub_zero]
  · rw [ha]; abel

/-- **The two-dimensional case.**  If the total complex has no three-boundaries — the
situation of the paper after the polygon-cylinder three-cell has been cancelled against the
replaced two-cell — then every two-cycle of the total complex is the image of a two-cycle of
the subcomplex. -/
theorem cycles_eq_image_of_relative_vanishing
    (dA₂ : A₂ →ₗ[R] A₁) (dB₃ : B₃ →ₗ[R] B₂) (dB₂ : B₂ →ₗ[R] B₁)
    (dQ₃ : Q₃ →ₗ[R] Q₂) (dQ₂ : Q₂ →ₗ[R] Q₁)
    (f₂ : A₂ →ₗ[R] B₂) (f₁ : A₁ →ₗ[R] B₁)
    (g₃ : B₃ →ₗ[R] Q₃) (g₂ : B₂ →ₗ[R] Q₂) (g₁ : B₁ →ₗ[R] Q₁)
    (hf₁ : Function.Injective f₁)
    (hexB₂ : ∀ b : B₂, g₂ b = 0 → ∃ a : A₂, f₂ a = b)
    (hg₃ : Function.Surjective g₃)
    (hchainF₂ : ∀ a : A₂, dB₂ (f₂ a) = f₁ (dA₂ a))
    (hchainG₃ : ∀ y : B₃, g₂ (dB₃ y) = dQ₃ (g₃ y))
    (hchainG₂ : ∀ b : B₂, g₁ (dB₂ b) = dQ₂ (g₂ b))
    (hB₃ : ∀ y : B₃, dB₃ y = 0)
    (hQ : ∀ q : Q₂, dQ₂ q = 0 → ∃ q₃ : Q₃, dQ₃ q₃ = q)
    (z : B₂) (hz : dB₂ z = 0) :
    ∃ a : A₂, dA₂ a = 0 ∧ z = f₂ a := by
  obtain ⟨a, y, ha, hzy⟩ :=
    h2_surjective_of_relative_vanishing dA₂ dB₃ dB₂ dQ₃ dQ₂ f₂ f₁ g₃ g₂ g₁ hf₁ hexB₂ hg₃
      hchainF₂ hchainG₃ hchainG₂ (fun y => by rw [hB₃ y, map_zero]) hQ z hz
  exact ⟨a, ha, by rw [hzy, hB₃ y, add_zero]⟩

/-- **`H₂(V, V₀) = H₂(V)` when `V₀` consists of vertices.**  Collapsing a subcomplex
concentrated in degree zero leaves the chain groups in degrees `1, 2, 3` unchanged, so the
vanishing of `H₂` of the space gives the vanishing of the relative group. -/
theorem h2_quotient_vanishing_of_h2_vanishing
    (dB₃ : B₃ →ₗ[R] B₂) (dB₂ : B₂ →ₗ[R] B₁) (dQ₃ : Q₃ →ₗ[R] Q₂) (dQ₂ : Q₂ →ₗ[R] Q₁)
    (e₃ : B₃ ≃ₗ[R] Q₃) (e₂ : B₂ ≃ₗ[R] Q₂) (e₁ : B₁ ≃ₗ[R] Q₁)
    (h₃ : ∀ y : B₃, dQ₃ (e₃ y) = e₂ (dB₃ y))
    (h₂ : ∀ b : B₂, dQ₂ (e₂ b) = e₁ (dB₂ b))
    (hB : ∀ z : B₂, dB₂ z = 0 → ∃ y : B₃, dB₃ y = z) :
    ∀ q : Q₂, dQ₂ q = 0 → ∃ q₃ : Q₃, dQ₃ q₃ = q := by
  intro q hq
  have hz : dB₂ (e₂.symm q) = 0 := by
    refine e₁.injective ?_
    rw [map_zero, ← h₂, LinearEquiv.apply_symm_apply, hq]
  obtain ⟨y, hy⟩ := hB _ hz
  exact ⟨e₃ y, by rw [h₃ y, hy, LinearEquiv.apply_symm_apply]⟩

/-- **The span form of the surjectivity.**  A spanning set of the two-cycles of the
subcomplex spans the two-cycles of the total complex. -/
theorem cycles_mem_span_image_of_relative_vanishing
    (dA₂ : A₂ →ₗ[R] A₁) (dB₃ : B₃ →ₗ[R] B₂) (dB₂ : B₂ →ₗ[R] B₁)
    (dQ₃ : Q₃ →ₗ[R] Q₂) (dQ₂ : Q₂ →ₗ[R] Q₁)
    (f₂ : A₂ →ₗ[R] B₂) (f₁ : A₁ →ₗ[R] B₁)
    (g₃ : B₃ →ₗ[R] Q₃) (g₂ : B₂ →ₗ[R] Q₂) (g₁ : B₁ →ₗ[R] Q₁)
    (hf₁ : Function.Injective f₁)
    (hexB₂ : ∀ b : B₂, g₂ b = 0 → ∃ a : A₂, f₂ a = b)
    (hg₃ : Function.Surjective g₃)
    (hchainF₂ : ∀ a : A₂, dB₂ (f₂ a) = f₁ (dA₂ a))
    (hchainG₃ : ∀ y : B₃, g₂ (dB₃ y) = dQ₃ (g₃ y))
    (hchainG₂ : ∀ b : B₂, g₁ (dB₂ b) = dQ₂ (g₂ b))
    (hB₃ : ∀ y : B₃, dB₃ y = 0)
    (hQ : ∀ q : Q₂, dQ₂ q = 0 → ∃ q₃ : Q₃, dQ₃ q₃ = q)
    (S : Set A₂) (hS : ∀ a : A₂, dA₂ a = 0 → a ∈ Submodule.span R S)
    (z : B₂) (hz : dB₂ z = 0) :
    z ∈ Submodule.span R (f₂ '' S) := by
  obtain ⟨a, ha, rfl⟩ :=
    cycles_eq_image_of_relative_vanishing dA₂ dB₃ dB₂ dQ₃ dQ₂ f₂ f₁ g₃ g₂ g₁ hf₁ hexB₂ hg₃
      hchainF₂ hchainG₃ hchainG₂ hB₃ hQ z hz
  have : Submodule.map f₂ (Submodule.span R S) ≤ Submodule.span R (f₂ '' S) := by
    rw [Submodule.map_span]
  exact this ⟨a, hS a ha, rfl⟩

end RelativeH2

/-! ## Putting steps 2 and 3 together over the group ring -/

section Assembly

open MonoidAlgebra

variable {Λ : Type*} [Group Λ] {ι : Type*}
variable {A₂ A₁ B₃ B₂ B₁ Q₃ Q₂ Q₁ : Type*}
  [AddCommGroup A₂] [Module (MonoidAlgebra ℤ Λ) A₂]
  [AddCommGroup A₁] [Module (MonoidAlgebra ℤ Λ) A₁]
  [AddCommGroup B₃] [Module (MonoidAlgebra ℤ Λ) B₃]
  [AddCommGroup B₂] [Module (MonoidAlgebra ℤ Λ) B₂]
  [AddCommGroup B₁] [Module (MonoidAlgebra ℤ Λ) B₁]
  [AddCommGroup Q₃] [Module (MonoidAlgebra ℤ Λ) Q₃]
  [AddCommGroup Q₂] [Module (MonoidAlgebra ℤ Λ) Q₂]
  [AddCommGroup Q₁] [Module (MonoidAlgebra ℤ Λ) Q₁]

/-- **The deck group permutes the components of `U`, so the chosen one spans.**  If an
element decomposes as a finite sum of contributions of the components, and each component is
a deck translate of the chosen one, then the element lies in the span of the chosen
component. -/
theorem mem_span_chosen_component (A : ι → AddSubgroup A₂) (i₀ : ι)
    (htrans : ∀ i : ι, ∃ g : Λ, ∀ x ∈ A i, ∃ y ∈ A i₀,
      x = (MonoidAlgebra.single g (1 : ℤ) : MonoidAlgebra ℤ Λ) • y)
    {a : A₂} (s : Finset ι) (f : ι → A₂) (hf : ∀ i ∈ s, f i ∈ A i) (hsum : a = ∑ i ∈ s, f i) :
    a ∈ Submodule.span (MonoidAlgebra ℤ Λ) (A i₀ : Set A₂) := by
  subst hsum
  refine Submodule.sum_mem _ fun i hi => ?_
  obtain ⟨g, hg⟩ := htrans i
  obtain ⟨y, hy, hxy⟩ := hg (f i) (hf i hi)
  rw [hxy]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hy)

/-- **The conclusion of steps 2 and 3 of the generation lemma.**  Assume:

* the relative complex of the pair has vanishing `H₂` (in the paper: `H₂(W̃, U) ≅ H₂(V) = 0`);
* the total complex has no three-boundaries (the two-dimensional situation after the cell
  cancellation);
* every two-cycle of the subcomplex `U` decomposes as a finite sum of two-cycles of its
  components, and the deck group carries each component to the chosen one.

Then every two-cycle of the total complex lies in the span, over `ℤ[π₁(W)]`, of the image of
the two-cycles of the chosen component — that is, `π₂(W) = ℤ[π₁(W)] · im π₂(X)`. -/
theorem generation_of_relative_vanishing
    (dA₂ : A₂ →ₗ[MonoidAlgebra ℤ Λ] A₁) (dB₃ : B₃ →ₗ[MonoidAlgebra ℤ Λ] B₂)
    (dB₂ : B₂ →ₗ[MonoidAlgebra ℤ Λ] B₁)
    (dQ₃ : Q₃ →ₗ[MonoidAlgebra ℤ Λ] Q₂) (dQ₂ : Q₂ →ₗ[MonoidAlgebra ℤ Λ] Q₁)
    (f₂ : A₂ →ₗ[MonoidAlgebra ℤ Λ] B₂) (f₁ : A₁ →ₗ[MonoidAlgebra ℤ Λ] B₁)
    (g₃ : B₃ →ₗ[MonoidAlgebra ℤ Λ] Q₃) (g₂ : B₂ →ₗ[MonoidAlgebra ℤ Λ] Q₂)
    (g₁ : B₁ →ₗ[MonoidAlgebra ℤ Λ] Q₁)
    (hf₁ : Function.Injective f₁)
    (hexB₂ : ∀ b : B₂, g₂ b = 0 → ∃ a : A₂, f₂ a = b)
    (hg₃ : Function.Surjective g₃)
    (hchainF₂ : ∀ a : A₂, dB₂ (f₂ a) = f₁ (dA₂ a))
    (hchainG₃ : ∀ y : B₃, g₂ (dB₃ y) = dQ₃ (g₃ y))
    (hchainG₂ : ∀ b : B₂, g₁ (dB₂ b) = dQ₂ (g₂ b))
    (hB₃ : ∀ y : B₃, dB₃ y = 0)
    (hQ : ∀ q : Q₂, dQ₂ q = 0 → ∃ q₃ : Q₃, dQ₃ q₃ = q)
    (A : ι → AddSubgroup A₂) (i₀ : ι)
    (hdecomp : ∀ a : A₂, dA₂ a = 0 → ∃ (s : Finset ι) (f : ι → A₂),
      (∀ i ∈ s, f i ∈ A i) ∧ a = ∑ i ∈ s, f i)
    (htrans : ∀ i : ι, ∃ g : Λ, ∀ x ∈ A i, ∃ y ∈ A i₀,
      x = (MonoidAlgebra.single g (1 : ℤ) : MonoidAlgebra ℤ Λ) • y)
    (z : B₂) (hz : dB₂ z = 0) :
    z ∈ Submodule.span (MonoidAlgebra ℤ Λ) (f₂ '' (A i₀ : Set A₂)) := by
  refine cycles_mem_span_image_of_relative_vanishing dA₂ dB₃ dB₂ dQ₃ dQ₂ f₂ f₁ g₃ g₂ g₁ hf₁
    hexB₂ hg₃ hchainF₂ hchainG₃ hchainG₂ hB₃ hQ (A i₀ : Set A₂) (fun a ha => ?_) z hz
  obtain ⟨s, f, hf, hsum⟩ := hdecomp a ha
  exact mem_span_chosen_component A i₀ htrans s f hf hsum

end Assembly

end FiniteChains
