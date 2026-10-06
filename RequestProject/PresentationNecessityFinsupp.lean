module

public import RequestProject.PresentationDictionary
public import RequestProject.HurewiczFinsupp

@[expose] public section

/-! The necessity dictionary for arbitrary presentations, with finitely supported chains. -/

namespace FiniteChains

variable {α J : Type*} [DecidableEq α] (ρ : J → FreeGroup α)
  (Nt : Subgroup (FreeGroup α)) [Nt.Normal] (hR : relSub ρ ≤ Nt)

include hR in
theorem fs_bdry2_ringEquivPres
    (c : J →₀ MonoidAlgebra ℤ (PresGroup ρ ⧸ presSub ρ Nt)) (i : α) :
    coverSecondBoundary Nt ρ (c.mapRange (ringEquivPres ρ Nt hR) (map_zero _)) i =
      ringEquivPres ρ Nt hR
        (boundaryMap (foxMatrixPres ρ) (foxMatrixPres_col_finite ρ) (presSub ρ Nt) c i) := by
  classical
  rw [coverSecondBoundary, Finsupp.linearCombination_apply,
    Finsupp.sum_mapRange_index (fun j =>
      zero_smul (CoverRing Nt) (coverFoxGradient Nt (ρ j)))]
  rw [boundaryMap_apply_coord, map_sum]
  rw [Finsupp.sum_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  change (∑ j ∈ c.support,
      ringEquivPres ρ Nt hR (c j) * proj Nt (fox i (ρ j))) = _
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul]
  congr 1
  exact (ringEquivPres_quot ρ Nt hR (fox i (ρ j))).symm

include hR in
theorem fs_liftsMod_of_foxSatMod (p : ℕ)
    (h : ∀ v : J →₀ MonoidAlgebra ℤ (PresGroup ρ),
      FoxSatMod p (foxMatrixPres ρ) v (presSub ρ Nt)) :
    LiftsMod (coverSecondBoundary Nt ρ).toAddMonoidHom p := by
  let E := ringEquivPres ρ Nt hR
  apply liftsMod_of_addEquiv
    (boundaryMap (foxMatrixPres ρ) (foxMatrixPres_col_finite ρ) (presSub ρ Nt))
    (coverSecondBoundary Nt ρ).toAddMonoidHom
    (Finsupp.mapRange.addEquiv E.toAddEquiv) (Finsupp.mapRange.addEquiv E.toAddEquiv)
    ?_ p (liftsMod_of_foxSatMod (foxMatrixPres ρ) (foxMatrixPres_col_finite ρ)
      (presSub ρ Nt) p h)
  intro c
  apply Finsupp.ext
  intro i
  exact fs_bdry2_ringEquivPres ρ Nt hR c i

include hR in
theorem fs_injective_boundary_of_foxSat
    (h : ∀ v : J →₀ MonoidAlgebra ℤ (PresGroup ρ),
      FoxSat (foxMatrixPres ρ) v (presSub ρ Nt)) :
    Function.Injective (coverSecondBoundary Nt ρ) := by
  let E := ringEquivPres ρ Nt hR
  let EC := Finsupp.mapRange.addEquiv (ι := J) E.toAddEquiv
  let ED := Finsupp.mapRange.addEquiv (ι := α) E.toAddEquiv
  have hcomm : ∀ c, coverSecondBoundary Nt ρ (EC c) =
      ED (boundaryMap (foxMatrixPres ρ) (foxMatrixPres_col_finite ρ) (presSub ρ Nt) c) := by
    intro c
    apply Finsupp.ext
    intro i
    exact fs_bdry2_ringEquivPres ρ Nt hR c i
  have hinj := (forall_foxSat_iff_injective (foxMatrixPres ρ)
    (foxMatrixPres_col_finite ρ) (presSub ρ Nt)).mp h
  intro c d he
  obtain ⟨x, rfl⟩ := EC.surjective c
  obtain ⟨y, rfl⟩ := EC.surjective d
  apply congrArg EC
  apply hinj
  apply ED.injective
  rw [← hcomm, ← hcomm]
  exact he

include hR in
theorem fs_hkey_presSub
    (hmod : ∀ p : ℕ, p.Prime → ∀ v : J →₀ MonoidAlgebra ℤ (PresGroup ρ),
      FoxSatMod p (foxMatrixPres ρ) v (presSub ρ Nt)) (hρ : ∀ j, ρ j ∈ Nt) :
    ∀ g ∈ presSub ρ Nt, ∀ n : ℕ, n ≠ 0 →
      g ^ n ∈ ⁅presSub ρ Nt, presSub ρ Nt⁆ → g ∈ ⁅presSub ρ Nt, presSub ρ Nt⁆ := by
  have hlift : ∀ p : ℕ, p.Prime →
      LiftsMod (coverSecondBoundary Nt ρ).toAddMonoidHom p :=
    fun p hp => fs_liftsMod_of_foxSatMod ρ Nt hR p (hmod p hp)
  rintro _ ⟨w, hw, rfl⟩ n hn hpow
  have hcommmap : ⁅presSub ρ Nt, presSub ρ Nt⁆ =
      ⁅Nt, Nt⁆.map (QuotientGroup.mk' (relSub ρ)) := by
    rw [presSub, ← Subgroup.map_commutator]
  have hcomap : w ^ n ∈ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅Nt, Nt⁆ := by
    have hmem : (QuotientGroup.mk' (relSub ρ)) (w ^ n) ∈
        ⁅Nt, Nt⁆.map (QuotientGroup.mk' (relSub ρ)) := by
      rw [← hcommmap, map_pow]
      exact hpow
    have hh : w ^ n ∈ ⁅Nt, Nt⁆ ⊔ (QuotientGroup.mk' (relSub ρ)).ker := by
      rw [← Subgroup.comap_map_eq]
      exact hmem
    rw [QuotientGroup.ker_mk', relSub, sup_comm] at hh
    exact hh
  have hw' := fs_mem_relComm_of_pow_mem Nt ρ hρ hlift hw hn hcomap
  have hh : w ∈ ⁅Nt, Nt⁆ ⊔ (QuotientGroup.mk' (relSub ρ)).ker := by
    rw [QuotientGroup.ker_mk', relSub, sup_comm]
    exact hw'
  rw [← Subgroup.comap_map_eq] at hh
  rw [hcommmap]
  exact hh

/-- The required torsion-freeness follows from all prime cycle tests for an arbitrary
presentation. Neither the generator set nor the relator set is assumed finite. -/
theorem fs_isMulTorsionFree_of_foxSatMod_pres (N : Subgroup (PresGroup ρ)) [N.Normal]
    (hmod : ∀ p : ℕ, p.Prime → ∀ v : J →₀ MonoidAlgebra ℤ (PresGroup ρ),
      FoxSatMod p (foxMatrixPres ρ) v N) :
    IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆)) := by
  let Nt := N.comap (QuotientGroup.mk' (relSub ρ))
  have hR : relSub ρ ≤ Nt := by
    intro r hr
    change (QuotientGroup.mk' (relSub ρ)) r ∈ N
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff r).mpr hr]
    exact N.one_mem
  have hNeq : presSub ρ Nt = N :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) N
  have hρ : ∀ j, ρ j ∈ Nt := fun j =>
    hR (Subgroup.subset_normalClosure (Set.mem_range_self j))
  have hm : ∀ p : ℕ, p.Prime → ∀ v : J →₀ MonoidAlgebra ℤ (PresGroup ρ),
      FoxSatMod p (foxMatrixPres ρ) v (presSub ρ Nt) := by
    rw [hNeq]
    exact hmod
  have hk := fs_hkey_presSub ρ Nt hR hm hρ
  apply isMulTorsionFree_map_commutator_of_pow N
  rwa [hNeq] at hk

section Compactness

universe u

/-- The algebraic necessity conclusion for an arbitrary presentation, with the homological
torsion-freeness input discharged by the finitely supported Hurewicz calculation. -/
theorem fs_exists_perfect_normal_of_cellChains
    {α J : Type u} [DecidableEq α] (ρ : J → FreeGroup α)
    (hchains : HasCellChainsLift (foxMatrixPres ρ)) :
    ∃ N : Subgroup (PresGroup ρ), N.Normal ∧
      (∀ p : ℕ, p.Prime → ∀ v : J →₀ MonoidAlgebra ℤ (PresGroup ρ),
        FoxSatMod p (foxMatrixPres ρ) v N) ∧
      (∀ v : J →₀ MonoidAlgebra ℤ (PresGroup ρ), FoxSat (foxMatrixPres ρ) v N) ∧
      ⁅N, N⁆ = N :=
  exists_perfect_normal_foxSatMod_of_finite_columns (foxMatrixPres ρ) hchains
    (foxMatrixPres_col_finite ρ) (fun N _ h => fs_isMulTorsionFree_of_foxSatMod_pres ρ N h)

end Compactness

end FiniteChains
