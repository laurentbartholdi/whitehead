module

public import RequestProject.CoverChainComplex
public import RequestProject.FoxCommutator

@[expose] public section

/-!
# From the requirements (2.2) to an acyclic cover

Section 2 of the paper produces a perfect normal subgroup `N ≤ G = π₁(K)` satisfying all
the requirements (2.2) and concludes that the corresponding cover `K_N` is acyclic:
`H₁(K_N) = N/[N, N] = 0` and `H₂(K_N) = ker ∂_{2,N} = 0`.

This file proves that implication algebraically, for the chain complex of the cover built
in `RequestProject/CoverChainComplex.lean`.  Requirements are the ones of
`RequestProject/FoxRequirement.lean`, applied to the Fox matrix `b i j = ∂r_j/∂x_i` of a
finite presentation, and perfectness of `N = Ñ / ⟪r_1, …, r_m⟫` is expressed as
`Ñ ≤ ⟪r_1, …, r_m⟫ ⊔ [Ñ, Ñ]`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

variable {α : Type*} [Fintype α] [DecidableEq α] {J : Type*} [Fintype J]
variable (Nsub : Subgroup (FreeGroup α)) [Nsub.Normal] (ρ : J → FreeGroup α)

omit [Fintype α] [DecidableEq α] in
theorem proj_eq_quotRingHom : proj Nsub = quotRingHom ℤ Nsub := rfl

/-- The Fox matrix `b i j = ∂r_j/∂x_i` of a presentation. -/
noncomputable def foxMatrix : α → J → FreeGroupRing α := fun i j => fox i (ρ j)

omit [Fintype α] in
/-- The requirements (2.2) for `Ñ` say exactly that `∂₂` is injective, i.e. that
`H₂(K_N) = 0`. -/
theorem bdry2_injective_of_foxSat
    (hsat : ∀ v : J →₀ FreeGroupRing α, FoxSat (foxMatrix ρ) v Nsub)
    (u : J → CoverRing Nsub) (hu : bdry2 Nsub ρ u = 0) : u = 0 := by
  classical
  set v : J →₀ FreeGroupRing α :=
    Finsupp.onFinset Finset.univ (fun j => liftQ Nsub (u j)) (by simp) with hv
  have hvapp : ∀ j, v j = liftQ Nsub (u j) := fun j => rfl
  have hproj : ∀ j, proj Nsub (v j) = u j := fun j => by rw [hvapp, proj_liftQ]
  have hbdry : ∀ i : α, proj Nsub (foxBoundary (foxMatrix ρ) v i) = 0 := by
    intro i
    have hcalc : proj Nsub (foxBoundary (foxMatrix ρ) v i)
        = ∑ j ∈ v.support, u j * proj Nsub (fox i (ρ j)) := by
      rw [foxBoundary, map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_mul, hproj, foxMatrix]
    have hfull : ∑ j ∈ v.support, u j * proj Nsub (fox i (ρ j))
        = ∑ j : J, u j * proj Nsub (fox i (ρ j)) := by
      refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
      have hzero : v j = 0 := by simpa using hj
      have : u j = 0 := by rw [← hproj j, hzero, map_zero]
      rw [this, zero_mul]
    have hu' : (∑ j : J, u j * proj Nsub (fox i (ρ j))) = 0 := congrFun hu i
    rw [hcalc, hfull, hu']
  have hvan : ∀ i : α, VanishesMod Nsub (foxBoundary (foxMatrix ρ) v i).coeff := fun i =>
    (vanishesMod_iff_quotRingHom_eq_zero Nsub _).2 (hbdry i)
  have hres := hsat v hvan
  funext j
  have : proj Nsub (v j) = 0 :=
    (vanishesMod_iff_quotRingHom_eq_zero Nsub (v j)).1 (hres j)
  rw [← hproj j, this]
  rfl

omit [Fintype α] in
/-- Conversely, injectivity of `∂₂` gives all the requirements (2.2) for `Ñ`; so the
requirements are exactly `H₂(K_N) = ker ∂₂ = 0`. -/
theorem foxSat_of_bdry2_injective
    (hinj : ∀ u : J → CoverRing Nsub, bdry2 Nsub ρ u = 0 → u = 0)
    (v : J →₀ FreeGroupRing α) : FoxSat (foxMatrix ρ) v Nsub := by
  classical
  intro hvan j
  have hbdry : ∀ i : α, proj Nsub (foxBoundary (foxMatrix ρ) v i) = 0 := fun i =>
    (vanishesMod_iff_quotRingHom_eq_zero Nsub _).1 (hvan i)
  have hu : bdry2 Nsub ρ (fun j => proj Nsub (v j)) = 0 := by
    funext i
    have hsupp : ∑ j : J, proj Nsub (v j) * proj Nsub (fox i (ρ j))
        = ∑ j ∈ v.support, proj Nsub (v j) * proj Nsub (fox i (ρ j)) := by
      refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
      have hzero : v j = 0 := by simpa using hj
      rw [hzero, map_zero, zero_mul]
    have hcalc : ∑ j ∈ v.support, proj Nsub (v j) * proj Nsub (fox i (ρ j))
        = proj Nsub (foxBoundary (foxMatrix ρ) v i) := by
      rw [foxBoundary, map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_mul, foxMatrix]
    show (∑ j : J, proj Nsub (v j) * proj Nsub (fox i (ρ j))) = 0
    rw [hsupp, hcalc, hbdry i]
  have := congrFun (hinj _ hu) j
  exact (vanishesMod_iff_quotRingHom_eq_zero Nsub (v j)).2 this

omit [Fintype α] in
/-- The requirements (2.2) for `Ñ` hold if and only if `∂₂` is injective. -/
theorem foxSat_iff_bdry2_injective :
    (∀ v : J →₀ FreeGroupRing α, FoxSat (foxMatrix ρ) v Nsub) ↔
      (∀ u : J → CoverRing Nsub, bdry2 Nsub ρ u = 0 → u = 0) :=
  ⟨bdry2_injective_of_foxSat Nsub ρ, foxSat_of_bdry2_injective Nsub ρ⟩

/-- If `N ≤ G` is perfect and `f : F → G` is onto with kernel `R`, then the preimage of
`N` lies in `R ⊔ [f⁻¹N, f⁻¹N]`. -/
theorem comap_le_ker_sup_commutator {F H : Type*} [Group F] [Group H] (f : F →* H)
    (hf : Function.Surjective f) {N : Subgroup H} (hN : ⁅N, N⁆ = N) :
    N.comap f ≤ f.ker ⊔ ⁅N.comap f, N.comap f⁆ := by
  intro w hw
  have hmapcomap : Subgroup.map f (N.comap f) = N := Subgroup.map_comap_eq_self_of_surjective hf N
  have hmap : Subgroup.map f ⁅N.comap f, N.comap f⁆ = N := by
    rw [Subgroup.map_commutator, hmapcomap, hN]
  have hfw : f w ∈ Subgroup.map f ⁅N.comap f, N.comap f⁆ := by rw [hmap]; exact hw
  obtain ⟨v, hv, hfv⟩ := hfw
  have hker : w * v⁻¹ ∈ f.ker := by
    simp [MonoidHom.mem_ker, map_mul, map_inv, hfv]
  have : w = (w * v⁻¹) * v := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hker) (Subgroup.mem_sup_right hv)

/-- **The cover attached to a perfect normal subgroup satisfying the requirements (2.2) is
acyclic.**  In the notation of Section 2: `H₂(K_N) = ker ∂_{2,N} = 0`, `H₁(K_N) = 0` and
`H̃₀(K_N) = 0`, so `K_N` is a connected acyclic cover of `K`. -/
theorem cover_acyclic_of_foxSat (hρ : ∀ j, ρ j ∈ Nsub)
    (hsat : ∀ v : J →₀ FreeGroupRing α, FoxSat (foxMatrix ρ) v Nsub)
    (hperf : Nsub ≤ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅Nsub, Nsub⁆) :
    (∀ u : J → CoverRing Nsub, bdry1 Nsub (bdry2 Nsub ρ u) = 0) ∧
      (∀ u : J → CoverRing Nsub, bdry2 Nsub ρ u = 0 → u = 0) ∧
      (∀ c : α → CoverRing Nsub, bdry1 Nsub c = 0 →
        ∃ u : J → CoverRing Nsub, bdry2 Nsub ρ u = c) ∧
      (∀ z : CoverRing Nsub, augQ Nsub z = 0 → ∃ c : α → CoverRing Nsub, bdry1 Nsub c = z) ∧
      (∀ c : α → CoverRing Nsub, augQ Nsub (bdry1 Nsub c) = 0) :=
  cover_acyclic Nsub ρ hρ hperf (bdry2_injective_of_foxSat Nsub ρ hsat)

/-- **The conclusion of Section 2, with the hypotheses of the paper.**  Let `Ñ ◁ F`
contain the normal closure `R` of the relators, so that `N = Ñ/R` is a normal subgroup of
`G = π₁(K) = F/R`.  If `N` is perfect and `Ñ` satisfies all the requirements (2.2), then
the chain complex of the cover `K_N` is acyclic. -/
theorem cover_acyclic_of_perfect_quotient
    (hR : Subgroup.normalClosure (Set.range ρ) ≤ Nsub)
    (hperf : ⁅Subgroup.map (QuotientGroup.mk' (Subgroup.normalClosure (Set.range ρ))) Nsub,
        Subgroup.map (QuotientGroup.mk' (Subgroup.normalClosure (Set.range ρ))) Nsub⁆
      = Subgroup.map (QuotientGroup.mk' (Subgroup.normalClosure (Set.range ρ))) Nsub)
    (hsat : ∀ v : J →₀ FreeGroupRing α, FoxSat (foxMatrix ρ) v Nsub) :
    (∀ u : J → CoverRing Nsub, bdry1 Nsub (bdry2 Nsub ρ u) = 0) ∧
      (∀ u : J → CoverRing Nsub, bdry2 Nsub ρ u = 0 → u = 0) ∧
      (∀ c : α → CoverRing Nsub, bdry1 Nsub c = 0 →
        ∃ u : J → CoverRing Nsub, bdry2 Nsub ρ u = c) ∧
      (∀ z : CoverRing Nsub, augQ Nsub z = 0 → ∃ c : α → CoverRing Nsub, bdry1 Nsub c = z) ∧
      (∀ c : α → CoverRing Nsub, augQ Nsub (bdry1 Nsub c) = 0) := by
  set R := Subgroup.normalClosure (Set.range ρ) with hRdef
  have hρ : ∀ j, ρ j ∈ Nsub := fun j =>
    hR (Subgroup.subset_normalClosure (Set.mem_range_self j))
  have hcomap : Subgroup.comap (QuotientGroup.mk' R) (Subgroup.map (QuotientGroup.mk' R) Nsub)
      = Nsub := Subgroup.comap_map_eq_self (by simpa using hR)
  have hperf' : Nsub ≤ R ⊔ ⁅Nsub, Nsub⁆ := by
    have h := comap_le_ker_sup_commutator (QuotientGroup.mk' R)
      (QuotientGroup.mk'_surjective R) hperf
    rw [hcomap, QuotientGroup.ker_mk'] at h
    exact h
  exact cover_acyclic_of_foxSat Nsub ρ hρ hsat hperf'

end FiniteChains
