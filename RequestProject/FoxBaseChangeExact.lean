module

public import RequestProject.BlockRelativeVanishing
public import RequestProject.UniversalCoverPi2
public import RequestProject.CoverHomologyOne

@[expose] public section

/-!
# Exactness of the Fox complex in degree one, and its base change

The (B2) half of the block argument needs, besides the CAT(0) input `H₂(W̃) = 0`, the injectivity
of `H₁(U) → H₁(W̃)`, where `U` is the full preimage of `X` in the universal cover of the double
mapping cylinder (`hU` in `RequestProject/BlockRelativeVanishing.lean`).  Geometrically `U` is a
disjoint union of copies of the universal cover `X̃`, so its first homology vanishes outright.

This file proves that, algebraically and with no hypotheses beyond the `π₁`-injectivity of the
substitution:

* `FiniteChains.univCover_exact_one` — **`H₁(X̃) = 0`**: a one-chain of the universal cover of a
  presentation complex killed by `∂₁` is the Fox boundary of a two-chain.  (From the Crowell
  sequence of `RequestProject/CoverHomologyOne.lean`: the cycles are the Fox vectors of the
  relator subgroup, and those are exactly the boundaries.)
* `FiniteChains.exists_preimage_base_change` — **base change along a subgroup preserves this
  kind of exactness**: if a matrix and a "boundary" matrix have their entries in `ℤ[H]`, and
  over `ℤ[H]` every cycle is a boundary, then the same holds over `ℤ[G]`.  The proof is the
  coset decomposition of `RequestProject/BaseChangeCycles.lean`: `ℤ[G]` is free over `ℤ[H]` on
  the cosets, and a cycle splits into its coset pieces, each of which is a cycle over `ℤ[H]`.
* `FiniteChains.BlockFox.foxBdryPush_exact_one` — **`H₁(U) = 0`**: every one-chain of the
  preimage killed by the boundary is the base-changed Fox boundary of a two-chain of the
  preimage.
* `FiniteChains.BlockFox.hU_of_chainMap` — the hypothesis `hU` of
  `FiniteChains.BlockFox.generates_of_absolute_model` follows, given that the inclusion of the
  preimage is a chain map in degree one which is injective on zero-chains and that the boundary
  of a boundary vanishes.
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

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

universe u

/-! ### Exactness of the Fox complex of the universal cover in degree one -/

section UnivCover

variable {α : Type u} [Fintype α] [DecidableEq α] {J : Type u} [Fintype J] (ρ : J → FreeGroup α)

/-- **`H₁` of the universal cover of a presentation complex vanishes.**  A one-chain killed by
`∂₁` is the Fox boundary of a two-chain: by the Crowell sequence it is the Fox vector of an
element of the relator subgroup, and the Fox vectors of relators are exactly the boundaries. -/
theorem univCover_exact_one (w : α → MonoidAlgebra ℤ (PresGroup ρ))
    (hw : bdry1 (relSub ρ) w = 0) :
    ∃ y : J → MonoidAlgebra ℤ (PresGroup ρ), foxBdry ρ y = w := by
  have hρ : ∀ j, ρ j ∈ relSub ρ := fun j => Subgroup.subset_normalClosure (Set.mem_range_self j)
  have hhom : ∀ v ∈ relSub ρ, ∃ r ∈ Subgroup.normalClosure (Set.range ρ),
      foxVec (relSub ρ) v = foxVec (relSub ρ) r := fun v hv => ⟨v, hv, rfl⟩
  obtain ⟨u, hu⟩ := (homologyOne_eq_zero_iff (relSub ρ) ρ hρ).2 hhom w hw
  refine ⟨u, ?_⟩
  funext i
  have := congrFun hu i
  simpa [foxBdry, bdry2, foxMatrixPres, proj_eq_quotRingHom] using this

end UnivCover

/-! ### Base change of exactness along a subgroup -/

section BaseChange

variable {G : Type*} [Group G] (H : Subgroup G)
variable {α J ι : Type*} [Fintype α] [Fintype J]

/-- **Base change along a subgroup preserves exactness.**  If the two matrices have their
entries in the group ring of the subgroup `H ≤ G`, and over `ℤ[H]` every vector killed by `B`
is in the image of `A`, then the same holds over `ℤ[G]`: `ℤ[G]` is free over `ℤ[H]` on the
cosets, so a cycle splits into coset pieces, each a cycle over `ℤ[H]`. -/
theorem exists_preimage_base_change (A : α → J → MonoidAlgebra ℤ H) (B : ι → α → MonoidAlgebra ℤ H)
    (hex : ∀ v : α → MonoidAlgebra ℤ H, (∀ i, ∑ a, v a * B i a = 0) →
      ∃ y : J → MonoidAlgebra ℤ H, ∀ a, ∑ j, y j * A a j = v a)
    (w : α → MonoidAlgebra ℤ G) (hw : ∀ i, ∑ a, w a * subRingHom H (B i a) = 0) :
    ∃ y : J → MonoidAlgebra ℤ G, ∀ a, ∑ j, y j * subRingHom H (A a j) = w a := by
  classical
  -- every coset slice of `w` is a cycle over `ℤ[H]`
  have hslice : ∀ g : G, ∀ i, ∑ a, slice H g (w a) * B i a = 0 := by
    intro g i
    have h := congrArg (slice H g) (hw i)
    rw [map_sum, map_zero] at h
    rw [← h]
    exact Finset.sum_congr rfl fun a _ => (slice_mul H g (w a) (B i a)).symm
  choose y hy using fun g : G => hex (fun a => slice H g (w a)) (hslice g)
  set S : Finset (G ⧸ H) :=
    (Finset.univ : Finset α).biUnion (fun a => (w a).coeff.support.image
      (fun p => (QuotientGroup.mk p : G ⧸ H))) with hS
  refine ⟨fun j => ∑ C ∈ S, single (Quotient.out C) (1 : ℤ) * subRingHom H (y (Quotient.out C) j),
    ?_⟩
  intro a
  have hdecomp : ∑ C ∈ S,
      single (Quotient.out C) (1 : ℤ) * subRingHom H (slice H (Quotient.out C) (w a)) = w a := by
    refine sum_cosetPieces_of_subset H (w a) S ?_
    exact Finset.subset_biUnion_of_mem
      (fun a => (w a).coeff.support.image (fun p => (QuotientGroup.mk p : G ⧸ H)))
      (Finset.mem_univ a)
  rw [← hdecomp]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [← hy (Quotient.out C) a, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, mul_assoc]

end BaseChange

/-! ### `H₁` of the preimage of `X` in the cover of the double mapping cylinder -/

namespace BlockFox

variable {α J α' J' : Type u}
  [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
  [Fintype α'] [DecidableEq α'] [Fintype J']
  {ρ : J → FreeGroup α} {ρ' : J' → FreeGroup α'}

/-- The image in `ℤ[G']` of the group-ring element `x_a - 1`: the boundary of the one-cell `a`
of the preimage of `X`. -/
noncomputable def pushEdge (f : PresMor ρ ρ') (a : α) : MonoidAlgebra ℤ (PresGroup ρ') :=
  f.pushRing (qgrp (relSub ρ) (FreeGroup.of a) - 1)

/-- The boundary `∂₁` of the preimage of `X`, in the base-changed coordinates. -/
noncomputable def bdry1Push (f : PresMor ρ ρ') (w : α → MonoidAlgebra ℤ (PresGroup ρ')) :
    MonoidAlgebra ℤ (PresGroup ρ') :=
  ∑ a, w a * pushEdge f a

omit [DecidableEq J] [Fintype α'] in
theorem bdry1Push_add (f : PresMor ρ ρ') (w v : α → MonoidAlgebra ℤ (PresGroup ρ')) :
    bdry1Push f (w + v) = bdry1Push f w + bdry1Push f v := by
  simp only [bdry1Push, Pi.add_apply, add_mul, Finset.sum_add_distrib]

omit [DecidableEq J] [Fintype α'] in
theorem bdry1Push_smul (f : PresMor ρ ρ') (c : MonoidAlgebra ℤ (PresGroup ρ'))
    (w : α → MonoidAlgebra ℤ (PresGroup ρ')) :
    bdry1Push f (c • w) = c * bdry1Push f w := by
  simp only [bdry1Push, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- The boundary `∂₁` of the preimage of `X`, as a map of `ℤ[G']`-modules. -/
noncomputable def bdry1PushL (f : PresMor ρ ρ') :
    (α → MonoidAlgebra ℤ (PresGroup ρ')) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')]
      MonoidAlgebra ℤ (PresGroup ρ') where
  toFun := bdry1Push f
  map_add' := bdry1Push_add f
  map_smul' := bdry1Push_smul f

omit [DecidableEq J] [Fintype α'] in
@[simp] theorem bdry1PushL_apply (f : PresMor ρ ρ') (w : α → MonoidAlgebra ℤ (PresGroup ρ')) :
    bdry1PushL f w = bdry1Push f w := rfl

omit [DecidableEq J] [Fintype α'] in
/-- **`H₁(U) = 0`.**  Every one-chain of the preimage of `X` killed by the boundary is the
base-changed Fox boundary of a two-chain: the preimage is a disjoint union of copies of the
universal cover of `X`, whose first homology vanishes; algebraically this is the base change of
`FiniteChains.univCover_exact_one` along the subgroup `f(G) ≤ G'`. -/
theorem foxBdryPush_exact_one (f : PresMor ρ ρ') (hinj : Function.Injective f.hom)
    (w : α → MonoidAlgebra ℤ (PresGroup ρ')) (hw : bdry1Push f w = 0) :
    ∃ y : J → MonoidAlgebra ℤ (PresGroup ρ'), foxBdryPush f y = w := by
  classical
  set H := f.hom.range with hH
  set A : α → J → MonoidAlgebra ℤ H := fun a j => imRing f hinj (foxMatrixPres ρ a j) with hA
  set B : Unit → α → MonoidAlgebra ℤ H :=
    fun _ a => imRing f hinj (qgrp (relSub ρ) (FreeGroup.of a) - 1) with hB
  -- the statement over `ℤ[H]`, transported from `ℤ[G]` along the isomorphism `imRing`
  have hex : ∀ v : α → MonoidAlgebra ℤ H, (∀ i, ∑ a, v a * B i a = 0) →
      ∃ y : J → MonoidAlgebra ℤ H, ∀ a, ∑ j, y j * A a j = v a := by
    intro v hv
    have hinvmk : ∀ x : MonoidAlgebra ℤ (PresGroup ρ), imRingInv f hinj (imRing f hinj x) = x := by
      intro x
      exact imRing_injective f hinj (by rw [imRing_imRingInv])
    have hv' : bdry1 (relSub ρ) (fun a => imRingInv f hinj (v a)) = 0 := by
      have h := congrArg (imRingInv f hinj) (hv ())
      rw [map_sum, map_zero] at h
      rw [bdry1, ← h]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, hB, hinvmk]
    obtain ⟨u, hu⟩ := univCover_exact_one ρ (fun a => imRingInv f hinj (v a)) hv'
    refine ⟨fun j => imRing f hinj (u j), fun a => ?_⟩
    have hu' := congrFun hu a
    calc ∑ j, imRing f hinj (u j) * A a j
        = imRing f hinj (∑ j, u j * foxMatrixPres ρ a j) := by
            rw [map_sum]
            exact Finset.sum_congr rfl fun j _ => by rw [map_mul, hA]
      _ = imRing f hinj (imRingInv f hinj (v a)) := by
            rw [show (∑ j, u j * foxMatrixPres ρ a j) = foxBdry ρ u a from rfl, hu']
      _ = v a := imRing_imRingInv f hinj (v a)
  have hwB : ∀ i : Unit, ∑ a, w a * subRingHom H (B i a) = 0 := by
    intro _
    rw [← hw, bdry1Push]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hB, subRingHom_imRing, pushEdge]
  obtain ⟨y, hy⟩ := exists_preimage_base_change H A B hex w hwB
  refine ⟨y, ?_⟩
  funext a
  rw [foxBdryPush_apply, ← hy a]
  exact Finset.sum_congr rfl fun j _ => by rw [hA, subRingHom_imRing]

variable {Q : Type*} [AddCommGroup Q] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q]

omit [DecidableEq J] [Fintype α'] in
/-- **The hypothesis `hU` of the block argument, discharged.**  If the inclusion of the preimage
of `X` is a chain map in degree one which is injective on zero-chains, and the boundary of a
boundary vanishes in the cover of the double mapping cylinder, then a one-chain of the preimage
which bounds in the cover already bounds in the preimage — because it is then a cycle of the
preimage, and `H₁(U) = 0`. -/
theorem hU_of_chainMap (f : PresMor ρ ρ') (hinj : Function.Injective f.hom)
    (bq : Q →ₗ[MonoidAlgebra ℤ (PresGroup ρ')] (α' → MonoidAlgebra ℤ (PresGroup ρ')))
    (f₁ : (α → MonoidAlgebra ℤ (PresGroup ρ')) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')]
      (α' → MonoidAlgebra ℤ (PresGroup ρ')))
    (bdry₁' : (α' → MonoidAlgebra ℤ (PresGroup ρ')) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')]
      MonoidAlgebra ℤ (PresGroup ρ'))
    (f₀ : MonoidAlgebra ℤ (PresGroup ρ') →ₗ[MonoidAlgebra ℤ (PresGroup ρ')]
      MonoidAlgebra ℤ (PresGroup ρ'))
    (hf₀ : Function.Injective f₀)
    (hchain₁ : ∀ w, bdry₁' (f₁ w) = f₀ (bdry1Push f w))
    (hdd₁ : ∀ z, bdry₁' (bdry₂model (Q := Q) bq z) = 0) :
    ∀ w, (∃ z, bdry₂model (Q := Q) bq z = f₁ w) → ∃ a, foxBdryPush f a = w := by
  rintro w ⟨z, hz⟩
  have h1 : f₀ (bdry1Push f w) = 0 := by
    rw [← hchain₁ w, ← hz, hdd₁ z]
  have h2 : bdry1Push f w = 0 := hf₀ (by rw [h1, map_zero])
  exact foxBdryPush_exact_one f hinj w h2

omit [Fintype α'] in
/-- **Property (B2) with the homological input reduced to the CAT(0) one.**  Equation (3.3) for
the structural map, where of the two homological hypotheses of
`FiniteChains.BlockFox.generates_of_absolute_model` only `H₂(W̃) = 0` remains: the injectivity of
`H₁(U) → H₁(W̃)` is now a theorem, the preimage of `X` having vanishing first homology. -/
theorem generates_of_absolute_chainMap {B₃ Q₃ Q₂ Q₁ : Type*}
    [AddCommGroup B₃] [Module (MonoidAlgebra ℤ (PresGroup ρ')) B₃]
    [AddCommGroup Q₃] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q₃]
    [AddCommGroup Q₂] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q₂]
    [AddCommGroup Q₁] [Module (MonoidAlgebra ℤ (PresGroup ρ')) Q₁]
    (f : PresMor ρ ρ') (hinj : Function.Injective f.hom)
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
    (bdry₁' : (α' → MonoidAlgebra ℤ (PresGroup ρ')) →ₗ[MonoidAlgebra ℤ (PresGroup ρ')]
      MonoidAlgebra ℤ (PresGroup ρ'))
    (f₀ : MonoidAlgebra ℤ (PresGroup ρ') →ₗ[MonoidAlgebra ℤ (PresGroup ρ')]
      MonoidAlgebra ℤ (PresGroup ρ'))
    (hf₁ : Function.Injective f₁)
    (hexB₂ : ∀ z, g₂ z = 0 → ∃ a, inclModel (Q := Q) f a = z)
    (hg₃ : Function.Surjective g₃)
    (hg₂surj : Function.Surjective g₂)
    (hg₂incl : ∀ a, g₂ (inclModel (Q := Q) f a) = 0)
    (hex₁ : ∀ y, g₁ y = 0 → ∃ w, f₁ w = y)
    (hf₀ : Function.Injective f₀)
    (hchain₁ : ∀ w, bdry₁' (f₁ w) = f₀ (bdry1Push f w))
    (hdd₁ : ∀ z, bdry₁' (bdry₂model (Q := Q) bq z) = 0)
    (habs : ∀ z, bdry₂model (Q := Q) bq z = 0 → ∃ y, Cancel.bdry₃ a₃ b₃ y = z)
    (hchainF₂ : ∀ a, bdry₂model (Q := Q) bq (inclModel f a) = f₁ (foxBdryPush f a))
    (hchainG₃ : ∀ y, g₂ (Cancel.bdry₃ a₃ b₃ y) = dQ₃ (g₃ y))
    (hchainG₂ : ∀ z, g₁ (bdry₂model (Q := Q) bq z) = dQ₂ (g₂ z))
    (hdd : ∀ y, bdry₂model (Q := Q) bq (Cancel.bdry₃ a₃ b₃ y) = 0) :
    Generates f :=
  generates_of_absolute_model f hinj bq a₃ b₃ dQ₃ dQ₂ f₁ g₃ g₂ g₁ hf₁ hexB₂ hg₃ hg₂surj hg₂incl
    hex₁ (hU_of_chainMap f hinj bq f₁ bdry₁' f₀ hf₀ hchain₁ hdd₁) habs hchainF₂ hchainG₃ hchainG₂ hdd

end BlockFox

end FiniteChains
