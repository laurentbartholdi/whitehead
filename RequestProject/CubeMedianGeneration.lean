import RequestProject.CubeGeneration
import RequestProject.CubeMedianGraph

/-!
# The generation step with the CAT(0) input in its median-graph form

`RequestProject/CubeGeneration.lean` derives steps 2 and 3 of the generation lemma from a cube
model of `V` given by the descending-cube axioms `FiniteChains.DescCubeStr`, and
`RequestProject/CubeMedianGraph.lean` derives those axioms from the statement that the
one-skeleton of `V` is a median graph — the standard combinatorial characterisation of the
CAT(0) cube complexes.  This file composes the two.

* `FiniteChains.cycles_bounded_of_median_model` — every two-cycle of the relative complex
  bounds;
* `FiniteChains.generation_of_median_model` — the conclusion of steps 2 and 3 of the
  generation lemma, with no hypothesis on `H₂(V)`.
-/

namespace FiniteChains

open MonoidAlgebra

universe u

section MedianCycles

variable {Vx : Type u} [LinearOrder Vx] (G : MedianGraph Vx)

/-- **Every two-cycle of the relative complex bounds, once the relative complex is the
cellular chain complex of a three-dimensional cube complex whose one-skeleton is a median
graph.** -/
theorem cycles_bounded_of_median_model {Q₃ Q₂ Q₁ : Type*}
    (dQ₃ : Q₃ → Q₂) (dQ₂ : Q₂ → Q₁) (zero₁ : Q₁)
    (e₃ : (G.toDescCubeStr.CbC →₀ ℤ) → Q₃) (e₂ : (G.toDescCubeStr.SqC →₀ ℤ) ≃ Q₂)
    (e₁ : (G.toDescCubeStr.EdgeC →₀ ℤ) → Q₁)
    (he₁ : Function.Injective e₁) (he₁0 : e₁ 0 = zero₁)
    (h₃ : ∀ y : G.toDescCubeStr.CbC →₀ ℤ, dQ₃ (e₃ y) = e₂ (G.toDescCubeStr.d₃ y))
    (h₂ : ∀ x : G.toDescCubeStr.SqC →₀ ℤ, dQ₂ (e₂ x) = e₁ (G.toDescCubeStr.d₂ x)) :
    ∀ q : Q₂, dQ₂ q = zero₁ → ∃ q₃ : Q₃, dQ₃ q₃ = q :=
  cycles_bounded_of_cube_model G.toDescCubeStr dQ₃ dQ₂ zero₁ e₃ e₂ e₁ he₁ he₁0 h₃ h₂

end MedianCycles

section Assembly

variable {Vx : Type u} [LinearOrder Vx]
variable {Λ : Type*} [Group Λ] {κ : Type*}
variable {A₂ A₁ B₃ B₂ B₁ Q₃ Q₂ Q₁ : Type*}
  [AddCommGroup A₂] [Module (MonoidAlgebra ℤ Λ) A₂]
  [AddCommGroup A₁] [Module (MonoidAlgebra ℤ Λ) A₁]
  [AddCommGroup B₃] [Module (MonoidAlgebra ℤ Λ) B₃]
  [AddCommGroup B₂] [Module (MonoidAlgebra ℤ Λ) B₂]
  [AddCommGroup B₁] [Module (MonoidAlgebra ℤ Λ) B₁]
  [AddCommGroup Q₃] [Module (MonoidAlgebra ℤ Λ) Q₃]
  [AddCommGroup Q₂] [Module (MonoidAlgebra ℤ Λ) Q₂]
  [AddCommGroup Q₁] [Module (MonoidAlgebra ℤ Λ) Q₁]

/-- **Steps 2 and 3 of the generation lemma from the median-graph description of `V`.**

This is `FiniteChains.generation_of_cube_model` with the descending-cube axioms replaced by
the hypothesis that the one-skeleton of the at most three-dimensional cube complex `V` is a
median graph.  No hypothesis on `H₂(V)` is assumed. -/
theorem generation_of_median_model (G : MedianGraph Vx)
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
    -- the median model of `V` in degrees `1, 2, 3`
    (e₃ : (G.toDescCubeStr.CbC →₀ ℤ) → Q₃) (e₂ : (G.toDescCubeStr.SqC →₀ ℤ) ≃ Q₂)
    (e₁ : (G.toDescCubeStr.EdgeC →₀ ℤ) → Q₁)
    (he₁ : Function.Injective e₁) (he₁0 : e₁ 0 = 0)
    (hmod₃ : ∀ y : G.toDescCubeStr.CbC →₀ ℤ, dQ₃ (e₃ y) = e₂ (G.toDescCubeStr.d₃ y))
    (hmod₂ : ∀ x : G.toDescCubeStr.SqC →₀ ℤ, dQ₂ (e₂ x) = e₁ (G.toDescCubeStr.d₂ x))
    (A : κ → AddSubgroup A₂) (i₀ : κ)
    (hdecomp : ∀ a : A₂, dA₂ a = 0 → ∃ (s : Finset κ) (f : κ → A₂),
      (∀ i ∈ s, f i ∈ A i) ∧ a = ∑ i ∈ s, f i)
    (htrans : ∀ i : κ, ∃ g : Λ, ∀ x ∈ A i, ∃ y ∈ A i₀,
      x = (MonoidAlgebra.single g (1 : ℤ) : MonoidAlgebra ℤ Λ) • y)
    (z : B₂) (hz : dB₂ z = 0) :
    z ∈ Submodule.span (MonoidAlgebra ℤ Λ) (f₂ '' (A i₀ : Set A₂)) :=
  generation_of_cube_model G.toDescCubeStr dA₂ dB₃ dB₂ dQ₃ dQ₂ f₂ f₁ g₃ g₂ g₁ hf₁ hexB₂ hg₃
    hchainF₂ hchainG₃ hchainG₂ hB₃ e₃ e₂ e₁ he₁ he₁0 hmod₃ hmod₂ A i₀ hdecomp htrans z hz

end Assembly

end FiniteChains
