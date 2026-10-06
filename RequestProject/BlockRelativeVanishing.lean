import RequestProject.BlockFoxModel

/-!
# Relative `H₂` of the pair from the absolute homology of the two halves

`RequestProject/BlockFoxModel.lean` proves property (B2) — equation (3.3) — for the chain model
of the double mapping cylinder `W` built over the Fox complex.  Two geometric inputs were left:
the exactness of the pair `(W̃, U)`, where `U` is the full preimage of `X`, and the vanishing of
the relative second homology, `H₂(W̃, U) = 0`, which the paper takes from the curvature
criterion (`hQvanish` in `FiniteChains.BlockFox.generates_of_fox_chain_model`).

This file removes the second one: relative vanishing is *deduced* from the two ends of the
usual homology sequence of a pair,

  `H₂(W̃) → H₂(W̃, U) → H₁(U) → H₁(W̃)`,

namely from

* `habs` — `H₂(W̃) = 0`: every two-cycle of the universal cover of `W` bounds.  This is the
  CAT(0) input of the paper, in the form in which the project proves it for cube complexes
  (`RequestProject/CubeCartanHadamard.lean`, `RequestProject/ConeCubeCover.lean`); and
* `hU` — the map `H₁(U) → H₁(W̃)` is injective: a one-chain of the preimage of `X` which bounds
  in `W̃` already bounds in `U`.  For the preimage of `X` this holds because each of its
  components is a copy of the universal cover of `X`, whose first homology vanishes.

Everything else used is structural: `g₂` is onto (the relative chains are a quotient), the
chains of `U` die in the quotient, and the quotient is exact in degree one.

* `FiniteChains.BlockFox.relative_vanishing_of_absolute` — the diagram chase;
* `FiniteChains.BlockFox.generates_of_absolute_model` — **property (B2) with the relative
  hypothesis replaced by the absolute one**: equation (3.3) for the structural map, the
  remaining homological input being `H₂(W̃) = 0` and the injectivity of `H₁(U) → H₁(W̃)`.
## Scope of this route (applicability warning)

The implication proved here is correct, but its hypothesis `habs` is **stronger than what the
article's Lemma "Generation in the pushout" supplies**.  That lemma allows an arbitrary
connected two-complex `X`, and its own Step 1 (the radial retraction) shows that `π₂(X)` injects
into `π₂(W)`; for a nonaspherical `X` this makes `H₂(W̃) = π₂(W) ≠ 0`, so `habs` is false.  A
concrete instance is `RequestProject/BlockSphereRegression.lean`.  The article's geometric input
is the *relative* vanishing `H₂(W̃, U) ≅ H₂(V, V₀) = H₂(V) = 0`, obtained from the space `V` in
which each component of `U` is collapsed to a vertex; property (B2) in that form is
`FiniteChains.BlockFox.generates_of_quotient_relative`
(`RequestProject/BlockRelativeQuotient.lean`), and the input is discharged from a cube-complex
model of `V` in `RequestProject/BlockCubeV.lean`.  The statements of this file should therefore
be read as an auxiliary implication, not as the article's argument.
-/

namespace FiniteChains

namespace BlockFox

universe u

variable {α J α' J' : Type u}
  [DecidableEq α] [Fintype J] [DecidableEq J] [DecidableEq α'] [Fintype J']
  {ρ : J → FreeGroup α} {ρ' : J' → FreeGroup α'}

section Relative

variable (f : PresMor ρ ρ')

variable {Q B₃ Q₃ Q₂ Q₁ : Type*}
  [AddCommGroup Q] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q]
  [AddCommGroup B₃] [Module (MonoidAlgebra ℤ (PresGroup ρ')) B₃]
  [AddCommGroup Q₃] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q₃]
  [AddCommGroup Q₂] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q₂]
  [AddCommGroup Q₁] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q₁]

/-- **The relative second homology of the pair vanishes.**  A diagram chase in the homology
sequence of the pair `(W̃, U)`: a relative two-cycle lifts to a two-chain `z` of `W̃` whose
boundary comes from `U`; that boundary bounds in `U` because `H₁(U) → H₁(W̃)` is injective, so
correcting `z` by a chain of `U` gives an absolute two-cycle, which bounds because
`H₂(W̃) = 0`; the correcting chain dies in the quotient. -/
theorem relative_vanishing_of_absolute
    (bq : Q →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] (α' → MonoidAlgebra ℤ (PresGroup ρ')))
    (a₃ : B₃ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] (J' → MonoidAlgebra ℤ (PresGroup ρ')))
    (b₃ : B₃ ≃ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q)
    (dQ₃ : Q₃ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q₂)
    (dQ₂ : Q₂ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q₁)
    (f₁ : (α → MonoidAlgebra ℤ (PresGroup ρ')) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')]
      (α' → MonoidAlgebra ℤ (PresGroup ρ')))
    (g₃ : B₃ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q₃)
    (g₂ : ((J' → MonoidAlgebra ℤ (PresGroup ρ')) × Q) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q₂)
    (g₁ : (α' → MonoidAlgebra ℤ (PresGroup ρ')) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q₁)
    (hg₂surj : Function.Surjective g₂)
    (hg₂incl : ∀ a, g₂ (inclModel (Q := Q) f a) = 0)
    (hex₁ : ∀ y, g₁ y = 0 → ∃ w, f₁ w = y)
    (hU : ∀ w, (∃ z, bdry₂model (Q := Q) bq z = f₁ w) → ∃ a, foxBdryPush f a = w)
    (habs : ∀ z, bdry₂model (Q := Q) bq z = 0 → ∃ y, Cancel.bdry₃ a₃ b₃ y = z)
    (hchainF₂ : ∀ a, bdry₂model (Q := Q) bq (inclModel f a) = f₁ (foxBdryPush f a))
    (hchainG₃ : ∀ y, g₂ (Cancel.bdry₃ a₃ b₃ y) = dQ₃ (g₃ y))
    (hchainG₂ : ∀ z, g₁ (bdry₂model (Q := Q) bq z) = dQ₂ (g₂ z)) :
    ∀ q, dQ₂ q = 0 → ∃ q₃, dQ₃ q₃ = q := by
  intro q hq
  obtain ⟨z, rfl⟩ := hg₂surj q
  have h1 : g₁ (bdry₂model (Q := Q) bq z) = 0 := by rw [hchainG₂ z, hq]
  obtain ⟨w, hw⟩ := hex₁ _ h1
  obtain ⟨a, ha⟩ := hU w ⟨z, hw.symm⟩
  have h2 : bdry₂model (Q := Q) bq (z - inclModel f a) = 0 := by
    rw [map_sub, hchainF₂ a, ha, hw, sub_self]
  obtain ⟨y, hy⟩ := habs _ h2
  refine ⟨g₃ y, ?_⟩
  have h3 : g₂ (Cancel.bdry₃ a₃ b₃ y) = g₂ z - g₂ (inclModel f a) := by
    rw [hy, map_sub]
  rw [← hchainG₃ y, h3, hg₂incl a, sub_zero]

/-- **Property (B2) with the homological input in absolute form.**  Equation (3.3) for the
structural map, with `H₂(W̃, U) = 0` replaced by the vanishing of `H₂(W̃)` — the CAT(0) input —
together with the injectivity of `H₁(U) → H₁(W̃)`, which holds because the components of the
preimage of `X` are copies of the universal cover of `X`. -/
theorem generates_of_absolute_model (hinj : Function.Injective f.hom)
    (bq : Q →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] (α' → MonoidAlgebra ℤ (PresGroup ρ')))
    (a₃ : B₃ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] (J' → MonoidAlgebra ℤ (PresGroup ρ')))
    (b₃ : B₃ ≃ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q)
    (dQ₃ : Q₃ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q₂)
    (dQ₂ : Q₂ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q₁)
    (f₁ : (α → MonoidAlgebra ℤ (PresGroup ρ')) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')]
      (α' → MonoidAlgebra ℤ (PresGroup ρ')))
    (g₃ : B₃ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q₃)
    (g₂ : ((J' → MonoidAlgebra ℤ (PresGroup ρ')) × Q) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q₂)
    (g₁ : (α' → MonoidAlgebra ℤ (PresGroup ρ')) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q₁)
    (hf₁ : Function.Injective f₁)
    (hexB₂ : ∀ z, g₂ z = 0 → ∃ a, inclModel (Q := Q) f a = z)
    (hg₃ : Function.Surjective g₃)
    (hg₂surj : Function.Surjective g₂)
    (hg₂incl : ∀ a, g₂ (inclModel (Q := Q) f a) = 0)
    (hex₁ : ∀ y, g₁ y = 0 → ∃ w, f₁ w = y)
    (hU : ∀ w, (∃ z, bdry₂model (Q := Q) bq z = f₁ w) → ∃ a, foxBdryPush f a = w)
    (habs : ∀ z, bdry₂model (Q := Q) bq z = 0 → ∃ y, Cancel.bdry₃ a₃ b₃ y = z)
    (hchainF₂ : ∀ a, bdry₂model (Q := Q) bq (inclModel f a) = f₁ (foxBdryPush f a))
    (hchainG₃ : ∀ y, g₂ (Cancel.bdry₃ a₃ b₃ y) = dQ₃ (g₃ y))
    (hchainG₂ : ∀ z, g₁ (bdry₂model (Q := Q) bq z) = dQ₂ (g₂ z))
    (hdd : ∀ y, bdry₂model (Q := Q) bq (Cancel.bdry₃ a₃ b₃ y) = 0) :
    Generates f :=
  generates_of_fox_chain_model f hinj bq a₃ b₃ dQ₃ dQ₂ f₁ g₃ g₂ g₁ hf₁ hexB₂ hg₃ hchainF₂
    hchainG₃ hchainG₂ hdd
    (relative_vanishing_of_absolute f bq a₃ b₃ dQ₃ dQ₂ f₁ g₃ g₂ g₁ hg₂surj hg₂incl hex₁ hU
      habs hchainF₂ hchainG₃ hchainG₂)

end Relative

end BlockFox

end FiniteChains
