import RequestProject.Pi2Dictionary
import RequestProject.CycleLiftingFinsupp
import RequestProject.CoverComplexFinsupp

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open MonoidAlgebra
universe u
variable {α J : Type u} {Nsub : Subgroup (FreeGroup α)} [Nsub.Normal]
variable {Q K : Type u} [Group Q]

theorem fs_mapDomain_prodMap_id_apply (Φ : (FreeGroup α ⧸ Nsub) →* Q)
    (u : ((FreeGroup α ⧸ Nsub) × J) →₀ ℤ) (q : Q) (j : J) :
    Finsupp.mapDomain (Prod.map (⇑Φ) (id : J → J)) u (q, j)
      = (MonoidAlgebra.mapDomainRingHom ℤ Φ (fsCoords Nsub J u j)).coeff q := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ =>
      rw [Finsupp.mapDomain_add, Finsupp.add_apply, h₁, h₂]
      simp [map_add]
  | single p n =>
      obtain ⟨q₀, j₀⟩ := p
      rw [Finsupp.mapDomain_single, fsCoords_single]
      show (Finsupp.single (Φ q₀, j₀) n : ((Q × J) →₀ ℤ)) (q, j)
        = (MonoidAlgebra.mapDomain Φ ((Finsupp.single j₀ (MonoidAlgebra.single q₀ n) : J →₀ CoverRing Nsub) j)).coeff q
      by_cases hj : j = j₀
      · subst hj
        rw [Finsupp.single_eq_same, MonoidAlgebra.mapDomain_single, MonoidAlgebra.coeff_single, Finsupp.single_apply,
          Finsupp.single_apply]
        by_cases hq : Φ q₀ = q
        · simp [hq]
        · simp [hq, Prod.ext_iff]
      · have hne : ((Φ q₀, j₀) : Q × J) ≠ (q, j) := fun hEq => hj (congrArg Prod.snd hEq).symm
        rw [Finsupp.single_eq_of_ne hj, Finsupp.single_apply, if_neg hne]
        simp

/-- **Pushing a two-chain of the cover to the next stage is zero iff its Fox coordinates
die.**  Here `Φ` is the map of deck groups and `g` the (injective) inclusion of the sets of
two-cells. -/
theorem fs_mapDomain_prodMap_eq_zero_iff (Φ : (FreeGroup α ⧸ Nsub) →* Q) (g : J → K)
    (hg : Function.Injective g) (u : ((FreeGroup α ⧸ Nsub) × J) →₀ ℤ) :
    Finsupp.mapDomain (Prod.map (⇑Φ) g) u = 0 ↔
      ∀ j, MonoidAlgebra.mapDomainRingHom ℤ Φ (fsCoords Nsub J u j) = 0 := by
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
    rw [← fs_mapDomain_prodMap_id_apply Φ u q j, h0]
    simp
  · intro h
    have h0 : Finsupp.mapDomain (Prod.map (⇑Φ) (id : J → J)) u = 0 := by
      refine Finsupp.ext fun p => ?_
      obtain ⟨q, j⟩ := p
      rw [fs_mapDomain_prodMap_id_apply Φ u q j, h j]
      simp
    rw [h0, Finsupp.mapDomain_zero]


variable [DecidableEq α]

/-- The actual cellular two-cycle condition, for arbitrary cell sets. -/
theorem fs_univCover_zero_pi2_iff (ρ : J → FreeGroup α)
    (Φ : PresGroup ρ →* Q) (g : J → K) (hg : Function.Injective g) :
    (∀ u : ((PresGroup ρ) × J) →₀ ℤ, bdry2 (univCover ρ) u = 0 →
        Finsupp.mapDomain (Prod.map (⇑Φ) g) u = 0) ↔
    (∀ v : J →₀ CoverRing (relSub ρ),
        (∀ i, ∑ j ∈ v.support, v j * foxMatrixPres ρ i j = 0) →
        Finsupp.mapDomain g
          (v.mapRange (MonoidAlgebra.mapDomainRingHom ℤ Φ) (map_zero _)) = 0) := by
  classical
  have hcycle : ∀ u : ((PresGroup ρ) × J) →₀ ℤ,
      bdry2 (univCover ρ) u = 0 ↔
      coverSecondBoundary (relSub ρ) ρ (fsCoords (relSub ρ) J u) = 0 := by
    intro u
    rw [fs_coverComplex_bdry2]
    exact (map_eq_zero_iff _ (fsCoords (relSub ρ) α).injective).symm
  constructor
  · intro H v hv
    let u := (fsCoords (relSub ρ) J).symm v
    have he : fsCoords (relSub ρ) J u = v := LinearEquiv.apply_symm_apply _ v
    have hc : bdry2 (univCover ρ) u = 0 := by
      rw [hcycle, he]
      apply Finsupp.ext
      intro i
      simpa only [fs_coverSecondBoundary_apply, Finsupp.zero_apply] using hv i
    have hz := H u hc
    rw [fs_mapDomain_prodMap_eq_zero_iff Φ g hg] at hz
    rw [mapDomain_mapRange_eq_zero_iff Φ g hg]
    simpa only [he] using hz
  · intro H u hu
    have hc := (hcycle u).mp hu
    have hz := H (fsCoords (relSub ρ) J u) (fun i => by
      have hi := congrArg (fun c => c i) hc
      simpa only [fs_coverSecondBoundary_apply, Finsupp.zero_apply] using hi)
    rw [mapDomain_mapRange_eq_zero_iff Φ g hg] at hz
    exact (fs_mapDomain_prodMap_eq_zero_iff Φ g hg u).mpr hz

end FiniteChains.Comb
