import RequestProject.ExampleSL25Group
import RequestProject.ExampleSL25
import RequestProject.HurewiczIso
import RequestProject.PresUnivCoverIso
import RequestProject.UniversalCoverPi2

/-! The integer rank of the second homotopy module of the example presentation. -/

namespace FiniteChains
namespace ExampleA

 theorem range_relA : Set.range relA = relsA := by
  ext w
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j
    · exact Or.inl rfl
    · right
      simp [relA, rel2, genX, genY, pow_succ, mul_assoc]
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · refine ⟨1, ?_⟩
      simp [relA, rel2, genX, genY, pow_succ, mul_assoc]

 theorem presGroup_relA_eq : PresGroup relA = GA := by
  change (FreeGroup (Fin 2) ⧸ Subgroup.normalClosure (Set.range relA)) =
    (FreeGroup (Fin 2) ⧸ Subgroup.normalClosure relsA)
  rw [range_relA]

noncomputable instance : Fintype (PresGroup relA) :=
  Fintype.ofEquiv SL25
    (presentedA_mulEquiv_SL25.toEquiv.symm.trans (Equiv.cast presGroup_relA_eq.symm))

 theorem card_presGroup_relA : Fintype.card (PresGroup relA) = 120 := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (Equiv.cast presGroup_relA_eq), card_GA]

abbrev RingA := CoverRing (relSub relA)
abbrev OneChains := Fin 2 → RingA

noncomputable def d1 : OneChains →ₗ[ℤ] RingA :=
  (bdry1Hom (relSub relA)).toIntLinearMap

noncomputable def d2 : OneChains →ₗ[ℤ] OneChains :=
  (bdry2Hom (relSub relA) relA).toIntLinearMap

noncomputable def augmentation : RingA →ₗ[ℤ] ℤ :=
  (augQ (relSub relA)).toAddMonoidHom.toIntLinearMap

 theorem range_d1 : LinearMap.range d1 = LinearMap.ker augmentation := by
  ext z
  constructor
  · rintro ⟨c, rfl⟩
    exact augQ_bdry1 (relSub relA) c
  · intro hz
    exact exists_bdry1_preimage (relSub relA) z hz

 theorem range_d2 : LinearMap.range d2 = LinearMap.ker d1 := by
  ext c
  constructor
  · rintro ⟨v, rfl⟩
    exact bdry1_bdry2 (relSub relA) relA (fun j => Comb.rel_mem_relSub relA j) v
  · intro hc
    exact exists_bdry2_preimage (relSub relA) relA (fun j => Comb.rel_mem_relSub relA j)
      (le_sup_left : relSub relA ≤ relSub relA ⊔ ⁅relSub relA, relSub relA⁆) c hc

 theorem finrank_ringA : Module.finrank ℤ RingA = 120 := by
  let e : RingA ≃ₗ[ℤ] (PresGroup relA → ℤ) := (MonoidAlgebra.coeffLinearEquiv ℤ).trans
    (Finsupp.linearEquivFunOnFinite ℤ ℤ (PresGroup relA))
  rw [e.finrank_eq, Module.finrank_pi, card_presGroup_relA]

 theorem finrank_oneChains : Module.finrank ℤ OneChains = 240 := by
  rw [Module.finrank_pi_fintype]
  simp [finrank_ringA]

/-- Rank-nullity over the integers for finite modules. -/
 theorem finite_finrank_nullity {R M N : Type} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Finite R M] [Module.Finite R N]
    (f : M →ₗ[R] N) :
    Module.finrank R (LinearMap.range f) + Module.finrank R (LinearMap.ker f) =
      Module.finrank R M := by
  have h := congrArg Cardinal.toNat f.rank_range_add_rank_ker
  rw [Cardinal.toNat_add (Module.rank_lt_aleph0 R _) (Module.rank_lt_aleph0 R _)] at h
  exact h

 theorem augmentation_surjective : Function.Surjective augmentation := by
  intro n
  exact ⟨MonoidAlgebra.single (1 : PresGroup relA) n, augQ_single _ _ _⟩

 theorem finrank_ker_augmentation : Module.finrank ℤ (LinearMap.ker augmentation) = 119 := by
  have h := finite_finrank_nullity augmentation
  rw [LinearMap.range_eq_top.mpr augmentation_surjective] at h
  have hr : Module.finrank ℤ (⊤ : Submodule ℤ ℤ) = 1 := by
    rw [(Submodule.topEquiv : (⊤ : Submodule ℤ ℤ) ≃ₗ[ℤ] ℤ).finrank_eq]
    exact Module.finrank_self ℤ
  rw [hr, finrank_ringA] at h
  omega

 theorem finrank_ker_d1 : Module.finrank ℤ (LinearMap.ker d1) = 121 := by
  have h := finite_finrank_nullity d1
  rw [range_d1, finrank_ker_augmentation, finrank_oneChains] at h
  omega

/-- The universal cover has 119 independent integral two-cycles. -/
 theorem finrank_ker_d2 : Module.finrank ℤ (LinearMap.ker d2) = 119 := by
  have h := finite_finrank_nullity d2
  rw [range_d2, finrank_ker_d1, finrank_oneChains] at h
  omega

/-- Coordinates on the two-chains of the path-class universal cover. -/
noncomputable def twoCoordinates :
    ((Comb.uCover (Comb.presComplex relA) PUnit.unit).F →₀ ℤ) →ₗ[ℤ] OneChains :=
  ((Comb.coords (relSub relA) (Fin 2)).toLinearMap.toAddMonoidHom.comp
    (Comb.chain2 (Comb.presUnivHom relA)).toAddMonoidHom).toIntLinearMap

 theorem twoCoordinates_bijective : Function.Bijective twoCoordinates := by
  constructor
  · intro x y h
    apply Finsupp.mapDomain_injective (Comb.uvFace_bijective relA).1
    exact (Comb.coords (relSub relA) (Fin 2)).injective h
  · intro v
    obtain ⟨u, hu⟩ := Comb.chain2_presUnivHom_surjective relA
      ((Comb.coords (relSub relA) (Fin 2)).symm v)
    refine ⟨u, ?_⟩
    change Comb.coords (relSub relA) (Fin 2) (Comb.chain2 (Comb.presUnivHom relA) u) = v
    rw [hu, LinearEquiv.apply_symm_apply]

 theorem twoCoordinates_cycle_iff
    (u : (Comb.uCover (Comb.presComplex relA) PUnit.unit).F →₀ ℤ) :
    u ∈ Comb.Pi2 (Comb.presComplex relA) PUnit.unit ↔ d2 (twoCoordinates u) = 0 := by
  rw [Comb.mem_pi2_iff_bdry2_eq_zero, Comb.univCover_bdry2_eq_zero_iff]
  change (∀ i : Fin 2, d2 (twoCoordinates u) i = 0) ↔ d2 (twoCoordinates u) = 0
  exact ⟨fun h => funext h, fun h i => congrFun h i⟩

/-- The repository's second homotopy module is the actual Fox boundary kernel. -/
noncomputable def pi2EquivFox :
    Comb.Pi2 (Comb.presComplex relA) PUnit.unit ≃ₗ[ℤ] LinearMap.ker d2 := by
  let e := LinearEquiv.ofBijective twoCoordinates twoCoordinates_bijective
  refine e.ofSubmodules _ _ ?_
  ext v
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (twoCoordinates_cycle_iff u).1 hu
  · intro hv
    refine ⟨e.symm v, (twoCoordinates_cycle_iff _).2 ?_, e.apply_symm_apply v⟩
    change d2 (e (e.symm v)) = 0
    rw [e.apply_symm_apply]
    exact hv

/-- The rank 119 part of Corollary B, for `Pi2` in the combinatorial model. -/
noncomputable def pi2EquivInt119 :
    Comb.Pi2 (Comb.presComplex relA) PUnit.unit ≃ₗ[ℤ] (Fin 119 → ℤ) :=
  pi2EquivFox.trans (LinearEquiv.ofFinrankEq (LinearMap.ker d2) (Fin 119 → ℤ)
    (by rw [finrank_ker_d2, Module.finrank_pi, Fintype.card_fin]))

 theorem finrank_pi2 : Module.finrank ℤ (Comb.Pi2 (Comb.presComplex relA) PUnit.unit) = 119 := by
  rw [pi2EquivFox.finrank_eq, finrank_ker_d2]

 theorem pi2_nontrivial : Nontrivial (Comb.Pi2 (Comb.presComplex relA) PUnit.unit) :=
  pi2EquivInt119.toEquiv.nontrivial

end ExampleA
end FiniteChains
