module

public import RequestProject.BlockQuotientModel

@[expose] public section

/-!
# Property (B2) with the geometric input in its article form: `H₂(W̃, U) = 0`

`RequestProject/BlockQuotientModel.lean` builds the relative chain complex of the pair
`(W̃, U)` as an honest quotient, but feeds it from the *absolute* vanishing `H₂(W̃) = 0`
(hypothesis `habs` of `FiniteChains.BlockFox.generates_of_quotient_model`).  That route is
sound as an implication, but its hypothesis is **not** available in the generality of the
article's Lemma "Generation in the pushout": for a nonaspherical `X` the radial retraction of
Step 1 of that proof injects `π₂(X)` into `π₂(W)`, so `H₂(W̃) = π₂(W) ≠ 0`.  See
`RequestProject/BlockSphereRegression.lean` for a concrete instance in which `habs` is false
while the conclusion (3.3) holds.

The article's own input is the *relative* vanishing

  `H₂(W̃, U) ≅ H₂(V, V₀) = H₂(V) = 0`,

where `V` is obtained from `W̃` by collapsing each component of `U` separately to a vertex and
`V₀` is the resulting set of vertices.  This file states property (B2) in exactly that form:
the relative complex is the constructed quotient of `RequestProject/BlockQuotientModel.lean`,
and the single homological hypothesis is that every relative two-cycle is the image of a
three-chain — that is, `H₂(W̃, U) = 0`.

* `FiniteChains.BlockFox.generates_of_quotient_relative` — **property (B2) from relative
  vanishing**: equation (3.3) for the structural map.  Besides the `π₁`-injectivity of the
  substitution (Step 1 of the article's proof) and the chain-level bookkeeping (the inclusion
  of the preimage is an injective chain map, `∂₂∘∂₃ = 0`), the only input is
  `H₂(W̃, U) = 0`.

Compared with `FiniteChains.BlockFox.generates_of_quotient_model` this statement needs *no*
hypothesis on `H₁(U) → H₁(W̃)` and no degree-one data (`bdry₁'`, `f₀`): those were needed only
to convert absolute vanishing into relative vanishing.  The relative hypothesis is discharged
from the cubical model of `V` in `RequestProject/BlockCubeV.lean`.
-/

namespace FiniteChains

namespace BlockFox

open MonoidAlgebra

universe u

variable {α J α' J' : Type u}
  [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
  [Fintype α'] [DecidableEq α'] [Fintype J']
  {ρ : J → FreeGroup α} {ρ' : J' → FreeGroup α'}

section Relative

variable {Q B₃ : Type u}
  [AddCommGroup Q] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q]
  [AddCommGroup B₃] [Module (MonoidAlgebra ℤ (PresGroup ρ')) B₃]

variable {f : PresMor ρ ρ'}
  {bq : Q →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] (α' → MonoidAlgebra ℤ (PresGroup ρ'))}
  {f₁ : (α → MonoidAlgebra ℤ (PresGroup ρ')) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')]
    (α' → MonoidAlgebra ℤ (PresGroup ρ'))}

/-- The relative boundary `C₃(W̃) → C₂(W̃, U)`: the boundary of the three-cells of the cover,
read in the relative complex.  Its image is what `H₂(W̃, U) = 0` asserts to be all of the
relative two-cycles. -/
noncomputable def relBdry₃
    (a₃ : B₃ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] (J' → MonoidAlgebra ℤ (PresGroup ρ')))
    (b₃ : B₃ ≃ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q) :
    B₃ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] RelTwo (Q := Q) f :=
  (subTwo (Q := Q) f).mkQ.comp (Cancel.bdry₃ a₃ b₃)

omit [Fintype α] [Fintype α'] in
/-- **Property (B2) with the article's geometric input.**  Equation (3.3) for the structural
map of the substitution, with the relative chain complex of the pair `(W̃, U)` constructed as
the quotient by the chains of the preimage of `X`, and with the single homological hypothesis
`hrel`, namely `H₂(W̃, U) = 0`: every relative two-cycle is the relative boundary of a
three-chain of `W̃`.

This is the form the article's proof actually establishes: the relative vanishing is obtained
there from `H₂(V) = 0` for the space `V` in which each component of `U` has been collapsed to a
vertex.  No vanishing of `H₂(W̃)` is assumed, and indeed none is available when `X` is
nonaspherical. -/
theorem generates_of_quotient_relative (hinj : Function.Injective f.hom)
    (a₃ : B₃ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] (J' → MonoidAlgebra ℤ (PresGroup ρ')))
    (b₃ : B₃ ≃ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q)
    (hf₁ : Function.Injective f₁)
    (hchainF₂ : ∀ a, bdry₂model (Q := Q) bq (inclModel f a) = f₁ (foxBdryPush f a))
    (hdd : ∀ y, bdry₂model (Q := Q) bq (Cancel.bdry₃ a₃ b₃ y) = 0)
    (hrel : ∀ q : RelTwo (Q := Q) f, relBdry₂ (bq := bq) hchainF₂ q = 0 →
      ∃ y : B₃, relBdry₃ (Q := Q) (f := f) a₃ b₃ y = q) :
    Generates f := by
  classical
  refine generates_of_fox_chain_model (Q := Q) (B₃ := B₃) (Q₃ := B₃)
    (Q₂ := RelTwo (Q := Q) f) (Q₁ := RelOne (α := α) f₁) f hinj bq a₃ b₃
    (relBdry₃ (Q := Q) (f := f) a₃ b₃) (relBdry₂ hchainF₂) f₁ LinearMap.id
    (subTwo (Q := Q) f).mkQ (subOne (α := α) f₁).mkQ hf₁ ?_ (fun y => ⟨y, rfl⟩)
    hchainF₂ (fun _ => rfl) (fun _ => rfl) hdd hrel
  · -- exactness of the pair in degree two: the kernel of the quotient map is the preimage
    intro z hz
    have h : z ∈ subTwo (Q := Q) f := (Submodule.Quotient.mk_eq_zero _).1 hz
    simpa only [subTwo, LinearMap.mem_range] using h

end Relative

end BlockFox

end FiniteChains
