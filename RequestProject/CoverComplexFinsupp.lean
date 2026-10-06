import RequestProject.CoverComplex
import RequestProject.CrowellFinsupp
import RequestProject.PresentationNecessityFinsupp

/-! Actual presentation covers with arbitrarily many edges and faces. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb

open MonoidAlgebra
universe u

variable {α J : Type u} [DecidableEq α] (N : Subgroup (FreeGroup α)) [N.Normal]

noncomputable def fsCoords (β : Type u) :
    (((FreeGroup α ⧸ N) × β) →₀ ℤ) ≃ₗ[ℤ] (β →₀ CoverRing N) :=
  (Finsupp.domLCongr (Equiv.prodComm (FreeGroup α ⧸ N) β)).trans
    ((Finsupp.curryLinearEquiv (R := ℤ)).trans
      (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv ℤ).symm))

omit [DecidableEq α] in
theorem fsCoords_apply (β : Type u) (c : ((FreeGroup α ⧸ N) × β) →₀ ℤ)
    (i : β) (q : FreeGroup α ⧸ N) : (fsCoords N β c i).coeff q = c (q, i) := by
  show ((Finsupp.equivMapDomain (Equiv.prodComm _ β) c).curry i) q = c (q, i)
  rw [Finsupp.curry_apply, Finsupp.equivMapDomain_apply]
  rfl

omit [DecidableEq α] in
theorem fsCoords_single (β : Type u) (q : FreeGroup α ⧸ N) (i : β) (n : ℤ) :
    fsCoords N β (Finsupp.single (q, i) n) =
      Finsupp.single i (MonoidAlgebra.single q n : CoverRing N) := by
  classical
  apply Finsupp.ext
  intro j
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro r
  rw [fsCoords_apply]
  by_cases hj : j = i <;> by_cases hr : r = q <;>
    simp [hj, hr]

theorem fsCoords_pathChain_liftPath_apply (L : List (α × Bool))
    (q : FreeGroup α ⧸ N) (i : α) :
    fsCoords N α (pathChain (liftPath L q)) i =
      (MonoidAlgebra.single q (1 : ℤ) : CoverRing N) * proj N (fox i (FreeGroup.mk L)) := by
  classical
  induction L generalizing q with
  | nil =>
      rw [show FreeGroup.mk ([] : List (α × Bool)) = 1 from rfl]
      simp
  | cons a L ih =>
      obtain ⟨k, b⟩ := a
      cases b
      · have hq : (MonoidAlgebra.single (q * (qof N k)⁻¹) (1 : ℤ) : CoverRing N) =
            (MonoidAlgebra.single q (1 : ℤ) : CoverRing N) * proj N (grp (FreeGroup.of k)⁻¹) := by
          rw [proj_grp, qgrp, QuotientGroup.mk_inv, MonoidAlgebra.single_mul_single, mul_one]
          rfl
        rw [liftPath_cons_false, pathChain_cons]
        simp only [Bool.false_eq_true, if_false, map_add, map_neg,
          Finsupp.add_apply, Finsupp.neg_apply]
        rw [ih, fsCoords_single, mk_cons_false, fox_mul, fox_inv,
          map_add, map_neg, map_mul, map_mul, mul_add, mul_neg,
          ← mul_assoc, ← mul_assoc, ← hq]
        congr 1
        by_cases h : i = k <;> simp [fox_of, h]
      · have hq : (MonoidAlgebra.single (q * qof N k) (1 : ℤ) : CoverRing N) =
            (MonoidAlgebra.single q (1 : ℤ) : CoverRing N) * proj N (grp (FreeGroup.of k)) := by
          rw [proj_grp, qgrp, MonoidAlgebra.single_mul_single, mul_one]
          rfl
        rw [liftPath_cons_true, pathChain_cons]
        simp only [if_true, map_add, Finsupp.add_apply]
        rw [ih, fsCoords_single, mk_cons_true, fox_mul, map_add, map_mul, mul_add,
          ← mul_assoc, ← hq]
        congr 1
        by_cases h : i = k <;> simp [fox_of, h]

variable (ρ : J → FreeGroup α) (hρ : ∀ j, ρ j ∈ N)

include hρ in
theorem fs_coverComplex_bdry1 (c : ((FreeGroup α ⧸ N) × α) →₀ ℤ) :
    coverFirstBoundary N (fsCoords N α c) = MonoidAlgebra.ofCoeff (bdry1 (coverComplex N ρ hρ) c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, MonoidAlgebra.ofCoeff_add]
  | single e n =>
      obtain ⟨q, i⟩ := e
      rw [fsCoords_single, bdry1_single]
      change coverFirstBoundary N (Finsupp.single i (MonoidAlgebra.single q n)) =
        n • (MonoidAlgebra.single (q * qof N i) (1 : ℤ) - MonoidAlgebra.single q (1 : ℤ))
      simp [coverFirstBoundary, qgrp, qof, smul_eq_mul, mul_sub,
        MonoidAlgebra.single_mul_single, smul_sub, Finsupp.smul_single]

include hρ in
theorem fs_coverComplex_bdry2 (c : ((FreeGroup α ⧸ N) × J) →₀ ℤ) :
    coverSecondBoundary N ρ (fsCoords N J c) =
      fsCoords N α (bdry2 (coverComplex N ρ hρ) c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, map_add]
  | single f n =>
      obtain ⟨q, j⟩ := f
      rw [fsCoords_single, bdry2_single, map_smul, coverSecondBoundary_single]
      apply Finsupp.ext
      intro i
      simp only [Finsupp.smul_apply, smul_eq_mul]
      rw [fsCoords_pathChain_liftPath_apply, FreeGroup.mk_toWord]
      change (MonoidAlgebra.single q n : CoverRing N) * proj N (fox i (ρ j)) =
        n • ((MonoidAlgebra.single q 1 : CoverRing N) * proj N (fox i (ρ j)))
      rw [show (MonoidAlgebra.single q n : CoverRing N) =
          n • (MonoidAlgebra.single q 1 : CoverRing N) by
        rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one], smul_mul_assoc]

include hρ in
/-- Acyclicity of the actual combinatorial cover from its finitely supported Fox complex,
without restricting the cardinality of either cell set. -/
theorem fs_coverComplex_isAcyclic
    (hperfect : N ≤ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆)
    (hinj : Function.Injective (coverSecondBoundary N ρ)) :
    IsAcyclic (coverComplex N ρ hρ) := by
  constructor
  · intro c d he
    apply (fsCoords N J).injective
    apply hinj
    rw [fs_coverComplex_bdry2 N ρ hρ, fs_coverComplex_bdry2 N ρ hρ, he]
  · intro c hc
    have he : coverFirstBoundary N (fsCoords N α c) = 0 := by
      rw [fs_coverComplex_bdry1 N ρ hρ, hc, MonoidAlgebra.ofCoeff_zero]
    obtain ⟨d, hd⟩ := exists_coverSecondBoundary_preimage N ρ hρ hperfect _ he
    refine ⟨(fsCoords N J).symm d, ?_⟩
    apply (fsCoords N α).injective
    rw [← fs_coverComplex_bdry2 N ρ hρ, LinearEquiv.apply_symm_apply, hd]
  · intro c hc
    have he : augQ N (MonoidAlgebra.ofCoeff c) = 0 := by rw [← coverComplex_augC hρ c, hc]
    obtain ⟨d, hd⟩ := exists_coverFirstBoundary_preimage N (MonoidAlgebra.ofCoeff c) he
    refine ⟨(fsCoords N α).symm d, ?_⟩
    apply MonoidAlgebra.ofCoeff_injective
    rw [← fs_coverComplex_bdry1 N ρ hρ, LinearEquiv.apply_symm_apply, hd]

include hρ in
theorem fs_presComplex_hasAcyclicRegularCover
    (hperfect : N ≤ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆)
    (hinj : Function.Injective (coverSecondBoundary N ρ)) :
    HasAcyclicRegularCover (presComplex ρ) :=
  ⟨coverComplex N ρ hρ, FreeGroup α ⧸ N, inferInstance, coverProj hρ, coverDeck hρ,
    coverProj_isCovering hρ, coverProj_isRegular hρ, coverComplex_isConnected hρ,
    fs_coverComplex_isAcyclic N ρ hρ hperfect hinj⟩

/-- A perfect normal subgroup satisfying the integral cycle tests gives an actual connected
acyclic regular cover of an arbitrary presentation complex. -/
theorem fs_presComplex_hasAcyclicRegularCover_of_perfect
    (H : Subgroup (PresGroup ρ)) [H.Normal]
    (hsat : ∀ v : J →₀ MonoidAlgebra ℤ (PresGroup ρ), FoxSat (foxMatrixPres ρ) v H)
    (hperf : ⁅H, H⁆ = H) : HasAcyclicRegularCover (presComplex ρ) := by
  let q := QuotientGroup.mk' (relSub ρ)
  let Nt := H.comap q
  have hR : relSub ρ ≤ Nt := by
    intro r hr
    change q r ∈ H
    have he : q r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
    rw [he]
    exact H.one_mem
  have hNeq : presSub ρ Nt = H :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) H
  have hm : ∀ v : J →₀ MonoidAlgebra ℤ (PresGroup ρ),
      FoxSat (foxMatrixPres ρ) v (presSub ρ Nt) := by
    rw [hNeq]
    exact hsat
  have hp : Nt ≤ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅Nt, Nt⁆ := by
    have he := comap_le_ker_sup_commutator q (QuotientGroup.mk'_surjective _) hperf
    simpa only [q, Nt, QuotientGroup.ker_mk', relSub] using he
  exact fs_presComplex_hasAcyclicRegularCover Nt ρ
    (fun j => hR (Subgroup.subset_normalClosure (Set.mem_range_self j))) hp
    (fs_injective_boundary_of_foxSat ρ Nt hR hm)

/-- The cell-chain hypothesis of necessity produces the cover with no finite-presentation
restriction and no torsion-freeness or cover-construction assumption. -/
theorem fs_presComplex_hasAcyclicRegularCover_of_cellChains
    (hchains : HasCellChainsLift (foxMatrixPres ρ)) :
    HasAcyclicRegularCover (presComplex ρ) := by
  obtain ⟨H, hN, _, hs, hp⟩ := fs_exists_perfect_normal_of_cellChains ρ hchains
  letI := hN
  exact fs_presComplex_hasAcyclicRegularCover_of_perfect ρ H hs hp

end FiniteChains.Comb
