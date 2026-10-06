module

public import RequestProject.CubeMedianGeneration
public import RequestProject.MedianGraphMetric

@[expose] public section

/-!
# The generation step with the CAT(0) input given by an actual median graph

`RequestProject/CubeMedianGeneration.lean` derives steps 2 and 3 of the generation lemma from
the hypothesis that the one-skeleton of `V` is a median graph in the sense of
`FiniteChains.MedianGraph` (a metric with unique medians).  This file states the same
conclusions for `FiniteChains.MedianSimpleGraph`, that is, when the one-skeleton is given as a
connected graph whose distance is the length of a shortest edge path — the standard
graph-theoretic model, for which the one-cells of the chain complex are the edges of the graph
and its two- and three-cells are the squares and three-cubes of the graph
(`RequestProject/MedianGraphCells.lean`).

* `FiniteChains.cycles_bounded_of_median_graph` — every two-cycle of the relative complex
  bounds;
* `FiniteChains.generation_of_median_graph` — the conclusion of steps 2 and 3 of the
  generation lemma, with no hypothesis on `H₂(V)`.
-/

namespace FiniteChains

open MonoidAlgebra

universe u

section MedianGraphCycles

variable {Vx : Type u} [LinearOrder Vx] (M : MedianSimpleGraph Vx)

/-- **Every two-cycle of the relative complex bounds, once the relative complex is the
cellular chain complex of a three-dimensional cube complex whose one-skeleton is a connected
median graph with the edge metric.** -/
theorem cycles_bounded_of_median_graph {Q₃ Q₂ Q₁ : Type*}
    (dQ₃ : Q₃ → Q₂) (dQ₂ : Q₂ → Q₁) (zero₁ : Q₁)
    (e₃ : (M.toDescCubeStr.CbC →₀ ℤ) → Q₃) (e₂ : (M.toDescCubeStr.SqC →₀ ℤ) ≃ Q₂)
    (e₁ : (M.toDescCubeStr.EdgeC →₀ ℤ) → Q₁)
    (he₁ : Function.Injective e₁) (he₁0 : e₁ 0 = zero₁)
    (h₃ : ∀ y : M.toDescCubeStr.CbC →₀ ℤ, dQ₃ (e₃ y) = e₂ (M.toDescCubeStr.d₃ y))
    (h₂ : ∀ x : M.toDescCubeStr.SqC →₀ ℤ, dQ₂ (e₂ x) = e₁ (M.toDescCubeStr.d₂ x)) :
    ∀ q : Q₂, dQ₂ q = zero₁ → ∃ q₃ : Q₃, dQ₃ q₃ = q :=
  cycles_bounded_of_median_model M.toMedianGraph dQ₃ dQ₂ zero₁ e₃ e₂ e₁ he₁ he₁0 h₃ h₂

end MedianGraphCycles

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

/-- **Steps 2 and 3 of the generation lemma when the one-skeleton of `V` is a median graph in
the graph-theoretic sense.**

This is `FiniteChains.generation_of_median_model` with the metric replaced by the edge metric
of a connected graph.  No hypothesis on `H₂(V)` is assumed. -/
theorem generation_of_median_graph (M : MedianSimpleGraph Vx)
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
    (e₃ : (M.toDescCubeStr.CbC →₀ ℤ) → Q₃) (e₂ : (M.toDescCubeStr.SqC →₀ ℤ) ≃ Q₂)
    (e₁ : (M.toDescCubeStr.EdgeC →₀ ℤ) → Q₁)
    (he₁ : Function.Injective e₁) (he₁0 : e₁ 0 = 0)
    (hmod₃ : ∀ y : M.toDescCubeStr.CbC →₀ ℤ, dQ₃ (e₃ y) = e₂ (M.toDescCubeStr.d₃ y))
    (hmod₂ : ∀ x : M.toDescCubeStr.SqC →₀ ℤ, dQ₂ (e₂ x) = e₁ (M.toDescCubeStr.d₂ x))
    (A : κ → AddSubgroup A₂) (i₀ : κ)
    (hdecomp : ∀ a : A₂, dA₂ a = 0 → ∃ (s : Finset κ) (f : κ → A₂),
      (∀ i ∈ s, f i ∈ A i) ∧ a = ∑ i ∈ s, f i)
    (htrans : ∀ i : κ, ∃ g : Λ, ∀ x ∈ A i, ∃ y ∈ A i₀,
      x = (MonoidAlgebra.single g (1 : ℤ) : MonoidAlgebra ℤ Λ) • y)
    (z : B₂) (hz : dB₂ z = 0) :
    z ∈ Submodule.span (MonoidAlgebra ℤ Λ) (f₂ '' (A i₀ : Set A₂)) :=
  generation_of_cube_model M.toDescCubeStr dA₂ dB₃ dB₂ dQ₃ dQ₂ f₂ f₁ g₃ g₂ g₁ hf₁ hexB₂ hg₃
    hchainF₂ hchainG₃ hchainG₂ hB₃ e₃ e₂ e₁ he₁ he₁0 hmod₃ hmod₂ A i₀ hdecomp htrans z hz

end Assembly

end FiniteChains
