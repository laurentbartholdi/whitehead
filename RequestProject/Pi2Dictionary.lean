module

public import RequestProject.UniversalCoverPi2
public import RequestProject.CycleLifting

@[expose] public section

/-!
# The condition "the inclusion is zero on `π₂`" in cellular and in Fox coordinates

Condition (1) of Theorem A is topological: for a chain `K = X₀ ⊂ X₁ ⊂ ⋯ ⊂ Xₙ` of
two-complexes the inclusion `X_r ⊂ X_{r+1}` is zero on `π₂`.  For a presentation complex
`π₂` is the module of cellular two-cycles of the universal cover
(`FiniteChains.Comb.univCover_bdry2_eq_zero_iff`), and the inclusion of complexes lifts to
the universal covers as the map of two-cells `(q, c) ↦ (Φ q, g c)`, where `Φ` is the map
induced on fundamental groups and `g` is the inclusion of the sets of two-cells.

This file proves that the resulting condition on cellular chains of the universal cover is
*equivalent* to the algebraic condition used in Section 2 (a Fox cycle over `ℤ[π₁(X_r)]`
has zero image in the chain module of `X_{r+1}`):
`FiniteChains.Comb.univCover_zero_pi2_iff`.

Thus the hypothesis carried by `FiniteChains.PresChain` is exactly condition (1) of the
paper, read in the combinatorial model, and nothing more.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Comb

open MonoidAlgebra

universe u

variable {α : Type u} [DecidableEq α] {J : Type u} [Fintype J] [DecidableEq J]
variable {Nsub : Subgroup (FreeGroup α)} [Nsub.Normal]
variable {Q : Type u} [Group Q] {K : Type u}

/-- The cellular two-chains of the cover, read as the free `ℤ[Q]`-module on the two-cells
of the base — the same as `FiniteChains.Comb.coords`, but with the target written as a
finitely supported family. -/
noncomputable def coordsF (Nsub : Subgroup (FreeGroup α)) (β : Type u) [Fintype β]
    [DecidableEq β] :
    (((FreeGroup α ⧸ Nsub) × β) →₀ ℤ) ≃ₗ[ℤ] (β →₀ CoverRing Nsub) :=
  (coords Nsub β).trans (Finsupp.linearEquivFunOnFinite ℤ (CoverRing Nsub) β).symm

omit [DecidableEq α] [Nsub.Normal] in
@[simp] theorem coordsF_apply (β : Type u) [Fintype β] [DecidableEq β]
    (c : ((FreeGroup α ⧸ Nsub) × β) →₀ ℤ) (i : β) :
    coordsF Nsub β c i = coords Nsub β c i := rfl

omit [DecidableEq α] in
/-- Pushing a cellular two-chain of the cover along the deck-group map, cell by cell, is
the coefficientwise image of its coordinate vector. -/
theorem mapDomain_prodMap_id_apply (Φ : (FreeGroup α ⧸ Nsub) →* Q)
    (u : ((FreeGroup α ⧸ Nsub) × J) →₀ ℤ) (q : Q) (j : J) :
    Finsupp.mapDomain (Prod.map (⇑Φ) (id : J → J)) u (q, j)
      = (MonoidAlgebra.mapDomainRingHom ℤ Φ (coords Nsub J u j)).coeff q := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ =>
      rw [Finsupp.mapDomain_add, Finsupp.add_apply, h₁, h₂]
      simp [map_add]
  | single p n =>
      obtain ⟨q₀, j₀⟩ := p
      rw [Finsupp.mapDomain_single, coords_single]
      show (Finsupp.single (Φ q₀, j₀) n : ((Q × J) →₀ ℤ)) (q, j)
        = (MonoidAlgebra.mapDomain Φ ((Pi.single j₀ (MonoidAlgebra.single q₀ n) : J → CoverRing Nsub) j)).coeff q
      by_cases hj : j = j₀
      · subst hj
        rw [Pi.single_eq_same, MonoidAlgebra.mapDomain_single, MonoidAlgebra.coeff_single, Finsupp.single_apply,
          Finsupp.single_apply]
        by_cases hq : Φ q₀ = q
        · simp [hq]
        · simp [hq, Prod.ext_iff]
      · have hne : ((Φ q₀, j₀) : Q × J) ≠ (q, j) := fun hEq => hj (congrArg Prod.snd hEq).symm
        rw [Pi.single_eq_of_ne hj, Finsupp.single_apply, if_neg hne]
        simp

omit [DecidableEq α] in
/-- **Pushing a two-chain of the cover to the next stage is zero iff its Fox coordinates
die.**  Here `Φ` is the map of deck groups and `g` the (injective) inclusion of the sets of
two-cells. -/
theorem mapDomain_prodMap_eq_zero_iff (Φ : (FreeGroup α ⧸ Nsub) →* Q) (g : J → K)
    (hg : Function.Injective g) (u : ((FreeGroup α ⧸ Nsub) × J) →₀ ℤ) :
    Finsupp.mapDomain (Prod.map (⇑Φ) g) u = 0 ↔
      ∀ j, MonoidAlgebra.mapDomainRingHom ℤ Φ (coords Nsub J u j) = 0 := by
  classical
  have hfac : (Prod.map (⇑Φ) g) = (Prod.map (id : Q → Q) g) ∘ (Prod.map (⇑Φ) (id : J → J)) := by
    funext p; rfl
  have hinj : Function.Injective (Prod.map (id : Q → Q) g) :=
    Function.Injective.prodMap Function.injective_id hg
  rw [hfac, Finsupp.mapDomain_comp]
  constructor
  · intro h j
    have h0 : Finsupp.mapDomain (Prod.map (⇑Φ) (id : J → J)) u = 0 := by
      refine Finsupp.mapDomain_injective hinj ?_
      rw [h, Finsupp.mapDomain_zero]
    apply MonoidAlgebra.coeff_injective
    refine Finsupp.ext fun q => ?_
    rw [← mapDomain_prodMap_id_apply Φ u q j, h0]
    simp
  · intro h
    have h0 : Finsupp.mapDomain (Prod.map (⇑Φ) (id : J → J)) u = 0 := by
      refine Finsupp.ext fun p => ?_
      obtain ⟨q, j⟩ := p
      rw [mapDomain_prodMap_id_apply Φ u q j, h j]
      simp
    rw [h0, Finsupp.mapDomain_zero]

omit [DecidableEq α] [Fintype J] [DecidableEq J] in
/-- The same statement in Fox coordinates: the image of a coefficient vector vanishes iff
each coefficient dies in the group ring of the next stage. -/
theorem mapDomain_mapRange_eq_zero_iff (Φ : (FreeGroup α ⧸ Nsub) →* Q) (g : J → K)
    (hg : Function.Injective g) (v : J →₀ CoverRing Nsub) :
    Finsupp.mapDomain g
        (Finsupp.mapRange (MonoidAlgebra.mapDomainRingHom ℤ Φ) (map_zero _) v) = 0 ↔
      ∀ j, MonoidAlgebra.mapDomainRingHom ℤ Φ (v j) = 0 := by
  classical
  constructor
  · intro h j
    have h0 : Finsupp.mapRange (MonoidAlgebra.mapDomainRingHom ℤ Φ) (map_zero _) v = 0 := by
      refine Finsupp.mapDomain_injective hg ?_
      rw [h, Finsupp.mapDomain_zero]
    have := congrArg (fun w : J →₀ MonoidAlgebra ℤ Q => w j) h0
    simpa using this
  · intro h
    have h0 : Finsupp.mapRange (MonoidAlgebra.mapDomainRingHom ℤ Φ) (map_zero _) v = 0 := by
      refine Finsupp.ext fun j => ?_
      simpa using h j
    rw [h0, Finsupp.mapDomain_zero]

variable [Fintype α]

/-- **The topological condition and the algebraic condition agree.**  For the two-complex
of a finite presentation, "the lift to the universal covers of the inclusion is zero on the
two-cycles" is equivalent to "a Fox cycle over `ℤ[π₁(X_r)]` has zero image in the chain
module of the next stage", which is the form in which Section 2 uses condition (1). -/
theorem univCover_zero_pi2_iff (ρ : J → FreeGroup α) (Φ : PresGroup ρ →* Q) (g : J → K)
    (hg : Function.Injective g) :
    (∀ u : ((FreeGroup α ⧸ relSub ρ) × J) →₀ ℤ, Comb.bdry2 (Comb.univCover ρ) u = 0 →
        Finsupp.mapDomain (Prod.map (⇑Φ) g) u = 0)
      ↔ (∀ v : J →₀ MonoidAlgebra ℤ (PresGroup ρ),
          (∀ a : α, ∑ c ∈ v.support, v c * foxMatrixPres ρ a c = 0) →
          Finsupp.mapDomain g
            (Finsupp.mapRange (MonoidAlgebra.mapDomainRingHom ℤ Φ) (map_zero _) v) = 0) := by
  classical
  constructor
  · intro H v hv
    set u := (coordsF (relSub ρ) J).symm v with hu
    have hcoords : ∀ j, coords (relSub ρ) J u j = v j := by
      intro j
      have : coordsF (relSub ρ) J u = v := (coordsF (relSub ρ) J).apply_symm_apply v
      rw [← coordsF_apply, this]
    have hcycle : Comb.bdry2 (Comb.univCover ρ) u = 0 := by
      refine (univCover_bdry2_eq_zero_iff ρ u).2 fun i => ?_
      have := hv i
      rw [sum_support_eq_sum_univ ρ v i] at this
      simpa [hcoords] using this
    have h0 := H u hcycle
    rw [mapDomain_prodMap_eq_zero_iff Φ g hg] at h0
    rw [mapDomain_mapRange_eq_zero_iff Φ g hg]
    intro j
    rw [← hcoords j]
    exact h0 j
  · intro H u hu
    set v := coordsF (relSub ρ) J u with hv
    have hcoords : ∀ j, coords (relSub ρ) J u j = v j := fun _ => rfl
    have hcycle : ∀ a : α, ∑ c ∈ v.support, v c * foxMatrixPres ρ a c = 0 := by
      intro a
      rw [sum_support_eq_sum_univ ρ v a]
      have := (univCover_bdry2_eq_zero_iff ρ u).1 hu a
      simpa [hcoords] using this
    have h0 := H v hcycle
    rw [mapDomain_mapRange_eq_zero_iff Φ g hg] at h0
    rw [mapDomain_prodMap_eq_zero_iff Φ g hg]
    intro j
    rw [hcoords j]
    exact h0 j

end Comb
end FiniteChains
