import RequestProject.FoxBaseChangeExact

/-!
# The relative complex of the pair as an honest quotient

`RequestProject/BlockRelativeVanishing.lean` and `RequestProject/FoxBaseChangeExact.lean` leave
property (B2) depending on a list of hypotheses of two kinds: *homological* ones (the vanishing
of `H₂(W̃)`) and *structural* ones describing the relative chain complex of the pair `(W̃, U)` —
that the relative chains are a quotient (`g₂`, `g₁` onto), that the chains of the preimage die in
it, and that it is exact in degrees one and two.

Here the relative complex is *built* — as the quotient by the image of the chains of the
preimage — so the structural hypotheses become theorems.  What is left of property (B2) is:

* the `π₁`-injectivity of the substitution (used already for the chosen copy of `X̃`);
* the injectivity of the inclusion of one-chains of the preimage;
* that the inclusion of the preimage is a chain map in degrees one and two;
* that the boundary of a boundary vanishes (in the two places where it is used);
* the CAT(0) input `H₂(W̃) = 0`.

`FiniteChains.BlockFox.generates_of_quotient_model` is the resulting statement, and
`RequestProject/BlockAbsoluteExample.lean` checks that its hypotheses are satisfiable.
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

open MonoidAlgebra

universe u

variable {α J α' J' : Type u}
  [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
  [Fintype α'] [DecidableEq α'] [Fintype J']
  {ρ : J → FreeGroup α} {ρ' : J' → FreeGroup α'}

section Quotient

variable {Q B₃ : Type u}
  [AddCommGroup Q] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q]
  [AddCommGroup B₃] [Module (MonoidAlgebra ℤ (PresGroup ρ')) B₃]

variable (f : PresMor ρ ρ')
  (bq : Q →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] (α' → MonoidAlgebra ℤ (PresGroup ρ')))
  (f₁ : (α → MonoidAlgebra ℤ (PresGroup ρ')) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')]
    (α' → MonoidAlgebra ℤ (PresGroup ρ')))

/-- The two-chains of the preimage of `X`, inside the two-chains of the cover of the double
mapping cylinder. -/
noncomputable def subTwo : Submodule (MonoidAlgebra ℤ (PresGroup ρ'))
    ((J' → MonoidAlgebra ℤ (PresGroup ρ')) × Q) :=
  LinearMap.range (inclModel (Q := Q) f)

/-- The one-chains of the preimage of `X`, inside the one-chains of the cover. -/
noncomputable def subOne : Submodule (MonoidAlgebra ℤ (PresGroup ρ'))
    (α' → MonoidAlgebra ℤ (PresGroup ρ')) :=
  LinearMap.range f₁

/-- The relative two-chains of the pair `(W̃, U)`. -/
abbrev RelTwo : Type u := ((J' → MonoidAlgebra ℤ (PresGroup ρ')) × Q) ⧸ subTwo (Q := Q) f

/-- The relative one-chains of the pair `(W̃, U)`. -/
abbrev RelOne : Type u := (α' → MonoidAlgebra ℤ (PresGroup ρ')) ⧸ subOne (α := α) f₁

variable {f bq f₁}

/-- The relative boundary `C₂(W̃, U) → C₁(W̃, U)`, induced by the boundary of the cover: it is
well defined because the inclusion of the preimage is a chain map. -/
noncomputable def relBdry₂
    (hchainF₂ : ∀ a, bdry₂model (Q := Q) bq (inclModel f a) = f₁ (foxBdryPush f a)) :
    RelTwo (Q := Q) f →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] RelOne (α := α) f₁ :=
  Submodule.mapQ _ _ (bdry₂model (Q := Q) bq) (by
    intro x hx
    simp only [subTwo, LinearMap.mem_range] at hx
    obtain ⟨a, rfl⟩ := hx
    show _ ∈ LinearMap.range f₁
    exact ⟨foxBdryPush f a, (hchainF₂ a).symm⟩)

omit [Fintype α'] in
/-- **Property (B2) with the relative complex constructed, not assumed.**  Equation (3.3) for the
structural map; the relative chain complex of the pair is the quotient by the chains of the
preimage of `X`, so the hypotheses about it are theorems.  What remains is the `π₁`-injectivity of
the substitution, the chain-map conditions for the inclusion of the preimage, the vanishing of
the boundary of a boundary, and the CAT(0) input `H₂(W̃) = 0`. -/
theorem generates_of_quotient_model (hinj : Function.Injective f.hom)
    (a₃ : B₃ →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] (J' → MonoidAlgebra ℤ (PresGroup ρ')))
    (b₃ : B₃ ≃ₗ[MonoidAlgebra ℤ (PresGroup ρ')] Q)
    (bdry₁' : (α' → MonoidAlgebra ℤ (PresGroup ρ')) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')]
      MonoidAlgebra ℤ (PresGroup ρ'))
    (f₀ : MonoidAlgebra ℤ (PresGroup ρ') →ₗ[MonoidAlgebra ℤ (PresGroup ρ')]
      MonoidAlgebra ℤ (PresGroup ρ'))
    (hf₁ : Function.Injective f₁)
    (hf₀ : Function.Injective f₀)
    (hchain₁ : ∀ w, bdry₁' (f₁ w) = f₀ (bdry1Push f w))
    (hdd₁ : ∀ z, bdry₁' (bdry₂model (Q := Q) bq z) = 0)
    (habs : ∀ z, bdry₂model (Q := Q) bq z = 0 → ∃ y, Cancel.bdry₃ a₃ b₃ y = z)
    (hchainF₂ : ∀ a, bdry₂model (Q := Q) bq (inclModel f a) = f₁ (foxBdryPush f a))
    (hdd : ∀ y, bdry₂model (Q := Q) bq (Cancel.bdry₃ a₃ b₃ y) = 0) :
    Generates f := by
  classical
  refine generates_of_absolute_chainMap (Q := Q) (B₃ := B₃) (Q₃ := B₃)
    (Q₂ := RelTwo (Q := Q) f) (Q₁ := RelOne (α := α) f₁) f hinj bq a₃ b₃
    ((subTwo (Q := Q) f).mkQ.comp (Cancel.bdry₃ a₃ b₃)) (relBdry₂ hchainF₂) f₁ LinearMap.id
    (subTwo (Q := Q) f).mkQ (subOne (α := α) f₁).mkQ bdry₁' f₀ hf₁ ?_ (fun y => ⟨y, rfl⟩)
    (Submodule.mkQ_surjective _) ?_ ?_ hf₀ hchain₁ hdd₁ habs hchainF₂ (fun _ => rfl) (fun _ => rfl)
    hdd
  · -- exactness of the pair in degree two: the kernel of the quotient map is the preimage
    intro z hz
    have h : z ∈ subTwo (Q := Q) f := (Submodule.Quotient.mk_eq_zero _).1 hz
    simpa only [subTwo, LinearMap.mem_range] using h
  · -- the chains of the preimage die in the quotient
    intro a
    exact (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self _ a)
  · -- exactness of the pair in degree one
    intro y hy
    have h : y ∈ subOne (α := α) f₁ := (Submodule.Quotient.mk_eq_zero _).1 hy
    simpa only [subOne, LinearMap.mem_range] using h

end Quotient

end BlockFox

end FiniteChains
