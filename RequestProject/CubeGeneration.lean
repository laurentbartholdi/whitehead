module

public import RequestProject.RelativeH2
public import RequestProject.CubeCartanHadamard

@[expose] public section

/-!
# Feeding the chain-level Cartan–Hadamard step into the generation lemma

`RequestProject/RelativeH2.lean` assembles steps 2 and 3 of the generation lemma of the paper
from the hypothesis

  `hQ : ∀ q, dQ₂ q = 0 → ∃ q₃, dQ₃ q₃ = q`,

which is the paper's `H₂(W̃, U) ≅ H₂(V, V₀) = H₂(V) = 0`.  Until now that hypothesis was an
unproved geometric input.  `RequestProject/CubeCartanHadamard.lean` proves it for the
cellular chains of an at most three-dimensional cube complex with the descending-cube
property (`FiniteChains.DescCubeStr`).

This file connects the two, without enlarging the algebraic interface:

* `FiniteChains.cycles_bounded_of_cube_model` — if the relative complex of the pair is
  identified, in degrees `1, 2, 3`, with the cellular chain complex of such a cube complex,
  then every two-cycle of the relative complex bounds;
* `FiniteChains.generation_of_cube_model` — the conclusion of steps 2 and 3 of the
  generation lemma with the hypothesis `H₂(V) = 0` **removed**: it is now derived from the
  cube model of `V`.  Compare `FiniteChains.generation_of_relative_vanishing`, which still
  carries `hQ` as an assumption.

All the other inputs of the generation step (exactness at `B₂`, surjectivity in degree
three, the two-dimensionality after the cell cancellation, and the transitive action of the
deck group on the components of `U`) are kept explicit, exactly as before.
-/

namespace FiniteChains

open MonoidAlgebra

section CubeModel

universe u

variable {Vx : Type u} [LinearOrder Vx] (S : DescCubeStr Vx)

/-- **Every two-cycle of the relative complex bounds, once the relative complex is the
cellular chain complex of a three-dimensional cube complex with the descending-cube
property.**

The data is an identification, in degrees `1, 2, 3`, of the given complex `Q_*` with the
cellular chains of the cube complex: `e₂` is a bijection in degree two, `e₁` is injective in
degree one, and the identifications commute with the boundary maps.  No linearity is needed
for this statement, so the interface stays minimal. -/
theorem cycles_bounded_of_cube_model {Q₃ Q₂ Q₁ : Type*}
    (dQ₃ : Q₃ → Q₂) (dQ₂ : Q₂ → Q₁) (zero₁ : Q₁)
    (e₃ : (S.CbC →₀ ℤ) → Q₃) (e₂ : (S.SqC →₀ ℤ) ≃ Q₂) (e₁ : (S.EdgeC →₀ ℤ) → Q₁)
    (he₁ : Function.Injective e₁) (he₁0 : e₁ 0 = zero₁)
    (h₃ : ∀ y : S.CbC →₀ ℤ, dQ₃ (e₃ y) = e₂ (S.d₃ y))
    (h₂ : ∀ x : S.SqC →₀ ℤ, dQ₂ (e₂ x) = e₁ (S.d₂ x)) :
    ∀ q : Q₂, dQ₂ q = zero₁ → ∃ q₃ : Q₃, dQ₃ q₃ = q := by
  intro q hq
  have hx : S.d₂ (e₂.symm q) = 0 := by
    refine he₁ ?_
    rw [← h₂, Equiv.apply_symm_apply, hq, he₁0]
  obtain ⟨c, hc⟩ := S.exists_d₃_eq _ hx
  refine ⟨e₃ c, ?_⟩
  rw [h₃ c, hc, Equiv.apply_symm_apply]

end CubeModel

section Assembly

open MonoidAlgebra

universe u

variable {Vx : Type u} [LinearOrder Vx]
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

/-- **Steps 2 and 3 of the generation lemma, with the vanishing of `H₂(V)` proved rather
than assumed.**

Compared with `FiniteChains.generation_of_relative_vanishing` the hypothesis

  `hQ : ∀ q : Q₂, dQ₂ q = 0 → ∃ q₃ : Q₃, dQ₃ q₃ = q`   (the paper's `H₂(V) = 0`)

has disappeared from the list of assumptions; in its place the relative complex is
identified, in degrees `1, 2, 3`, with the cellular chain complex of the cube complex `V`
described by `S : DescCubeStr Vx` — an at most three-dimensional cube complex in which the
edges pointing towards the base vertex span a cube (the combinatorial form of the CAT(0)
input of the paper).  The vanishing of the relative `H₂` is then a theorem, namely
`FiniteChains.DescCubeStr.exists_d₃_eq`.

The remaining hypotheses are the same as before and are listed explicitly: injectivity of
`f₁`, exactness at `B₂`, surjectivity of `g₃`, the chain-map identities, the absence of
three-boundaries in the total complex after the cell cancellation, and the decomposition of
two-cycles of `U` into components permuted transitively by the deck group. -/
theorem generation_of_cube_model (S : DescCubeStr Vx)
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
    -- the cube model of `V` in degrees `1, 2, 3`
    (e₃ : (S.CbC →₀ ℤ) → Q₃) (e₂ : (S.SqC →₀ ℤ) ≃ Q₂) (e₁ : (S.EdgeC →₀ ℤ) → Q₁)
    (he₁ : Function.Injective e₁) (he₁0 : e₁ 0 = 0)
    (hmod₃ : ∀ y : S.CbC →₀ ℤ, dQ₃ (e₃ y) = e₂ (S.d₃ y))
    (hmod₂ : ∀ x : S.SqC →₀ ℤ, dQ₂ (e₂ x) = e₁ (S.d₂ x))
    (A : ι → AddSubgroup A₂) (i₀ : ι)
    (hdecomp : ∀ a : A₂, dA₂ a = 0 → ∃ (s : Finset ι) (f : ι → A₂),
      (∀ i ∈ s, f i ∈ A i) ∧ a = ∑ i ∈ s, f i)
    (htrans : ∀ i : ι, ∃ g : Λ, ∀ x ∈ A i, ∃ y ∈ A i₀,
      x = (MonoidAlgebra.single g (1 : ℤ) : MonoidAlgebra ℤ Λ) • y)
    (z : B₂) (hz : dB₂ z = 0) :
    z ∈ Submodule.span (MonoidAlgebra ℤ Λ) (f₂ '' (A i₀ : Set A₂)) := by
  refine generation_of_relative_vanishing dA₂ dB₃ dB₂ dQ₃ dQ₂ f₂ f₁ g₃ g₂ g₁ hf₁ hexB₂ hg₃
    hchainF₂ hchainG₃ hchainG₂ hB₃ ?_ A i₀ hdecomp htrans z hz
  exact cycles_bounded_of_cube_model S (fun q => dQ₃ q) (fun q => dQ₂ q) 0 e₃ e₂ e₁ he₁ he₁0
    hmod₃ hmod₂

end Assembly

end FiniteChains
