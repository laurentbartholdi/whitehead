import RequestProject.FoxFinsupp
import RequestProject.CoverHomologyOne
import RequestProject.MagnusKernel

/-! The Crowell sequence with finite chains and arbitrary cell-index types. -/

namespace FiniteChains

variable {α : Type*} [DecidableEq α] (N : Subgroup (FreeGroup α)) [N.Normal]

@[simp] theorem coe_coverFoxGradient (w : FreeGroup α) :
    (coverFoxGradient N w : α → CoverRing N) = foxVec N w := rfl

theorem coverFoxGradient_mul {v : FreeGroup α} (hv : v ∈ N) (w : FreeGroup α) :
    coverFoxGradient N (v * w) = coverFoxGradient N v + coverFoxGradient N w := by
  apply Finsupp.ext
  intro i
  exact congrFun (foxVec_mul hv w) i

theorem coverFoxGradient_inv {v : FreeGroup α} (hv : v ∈ N) :
    coverFoxGradient N v⁻¹ = -coverFoxGradient N v := by
  apply Finsupp.ext
  intro i
  exact congrFun (foxVec_inv hv) i

theorem coverFoxGradient_zpow {v : FreeGroup α} (hv : v ∈ N) (n : ℤ) :
    coverFoxGradient N (v ^ n) = n • coverFoxGradient N v := by
  apply Finsupp.ext
  intro i
  exact congrFun (foxVec_zpow hv n) i

theorem coverFoxGradient_conj {r : FreeGroup α} (hr : r ∈ N) (f : FreeGroup α) :
    coverFoxGradient N (f * r * f⁻¹) = qgrp N f • coverFoxGradient N r := by
  apply Finsupp.ext
  intro i
  change foxVec N (f * r * f⁻¹) i = qgrp N f * foxVec N r i
  simpa only [proj_grp, Pi.smul_apply, smul_eq_mul] using congrFun (foxVec_conj hr f) i

@[simp] theorem coverFoxGradient_one : coverFoxGradient N (1 : FreeGroup α) = 0 := by
  ext i
  simp [coverFoxGradient]

theorem coverFoxGradient_eq_zero_iff {w : FreeGroup α} (hw : w ∈ N) :
    coverFoxGradient N w = 0 ↔ w ∈ ⁅N, N⁆ := by
  rw [← foxVec_eq_zero_iff N hw]
  exact ⟨fun h => congrArg (fun c : α →₀ CoverRing N => (c : α → CoverRing N)) h,
    fun h => Finsupp.ext (congrFun h)⟩

/-- Every finite one-cycle of a cover is the Fox vector of a word in its defining subgroup.
There is no assumption that the set of generators is finite. -/
theorem exists_mem_of_coverFirstBoundary_eq_zero (c : α →₀ CoverRing N)
    (hc : coverFirstBoundary N c = 0) :
    ∃ r ∈ N, c = coverFoxGradient N r := by
  classical
  let a : α → FreeGroupRing α := fun i => liftQ N (c i)
  let b : FreeGroupRing α := ∑ i ∈ c.support, a i * (grp (FreeGroup.of i) - 1)
  have hproja : ∀ i, proj N (a i) = c i := fun i => proj_liftQ N (c i)
  have hprojb : proj N b = 0 := by
    change proj N (∑ i ∈ c.support, a i * (grp (FreeGroup.of i) - 1)) = 0
    rw [map_sum]
    change (∑ i ∈ c.support, proj N (a i * (grp (FreeGroup.of i) - 1))) = 0
    have he : ∑ i ∈ c.support, proj N (a i * (grp (FreeGroup.of i) - 1)) =
        coverFirstBoundary N c := by
      change _ = ∑ i ∈ c.support, c i * (qgrp N (FreeGroup.of i) - 1)
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_mul, map_sub, proj_grp, map_one, hproja]
    rw [he, hc]
  have hfoxb : foxProj N b = (c : α → CoverRing N) := by
    funext j
    have hterm : ∀ i, foxLin j (a i * (grp (FreeGroup.of i) - 1)) =
        a i * (if j = i then 1 else 0) := by
      intro i
      rw [foxLin_mul, map_sub, aug_grp, map_one, sub_self,
        zero_smul, zero_add, map_sub]
      have h1 : foxLin j (1 : FreeGroupRing α) = 0 := by
        rw [← grp_one, foxLin_grp, fox_one]
      rw [h1, foxLin_grp, fox_of, sub_zero]
    change proj N (foxLin j b) = c j
    dsimp only [b]
    rw [map_sum]
    change proj N (∑ i ∈ c.support, foxLin j (a i * (grp (FreeGroup.of i) - 1))) = c j
    simp_rw [hterm]
    by_cases hj : j ∈ c.support
    · simpa [mul_ite, Finset.sum_ite_eq', hj] using hproja j
    · have hz : c j = 0 := by simpa using hj
      simp [mul_ite, hj, hz]
  obtain ⟨r, hr, he⟩ := foxProj_mem_foxMod N b hprojb
  refine ⟨r, hr, ?_⟩
  apply Finsupp.ext
  intro i
  exact congrFun (hfoxb.symm.trans he) i

variable {J : Type*} (ρ : J → FreeGroup α)

@[simp] theorem coverSecondBoundary_single (j : J) (x : CoverRing N) :
    coverSecondBoundary N ρ (Finsupp.single j x) = x • coverFoxGradient N (ρ j) :=
  Finsupp.linearCombination_single _ x j

/-- The Fox vector of every consequence of the relators is a finite two-boundary. -/
theorem exists_coverSecondBoundary_of_mem_normalClosure (hρ : ∀ j, ρ j ∈ N)
    {w : FreeGroup α} (hw : w ∈ Subgroup.normalClosure (Set.range ρ)) :
    ∃ c : J →₀ CoverRing N, coverSecondBoundary N ρ c = coverFoxGradient N w := by
  classical
  let T : Subgroup (FreeGroup α) :=
    { carrier := {v | v ∈ N ∧ ∃ c : J →₀ CoverRing N,
        coverSecondBoundary N ρ c = coverFoxGradient N v}
      one_mem' := ⟨N.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro v w ⟨hv, c, hc⟩ ⟨hw, d, hd⟩
        exact ⟨N.mul_mem hv hw, c + d, by
          rw [map_add, hc, hd, coverFoxGradient_mul N hv]⟩
      inv_mem' := by
        rintro w ⟨hw, c, hc⟩
        exact ⟨N.inv_mem hw, -c, by rw [map_neg, hc, coverFoxGradient_inv N hw]⟩ }
  haveI : T.Normal := by
    constructor
    rintro w ⟨hw, c, hc⟩ f
    refine ⟨Subgroup.Normal.conj_mem ‹N.Normal› w hw f, qgrp N f • c, ?_⟩
    rw [map_smul, hc, coverFoxGradient_conj N hw]
  have hrange : Set.range ρ ⊆ (T : Set (FreeGroup α)) := by
    rintro _ ⟨j, rfl⟩
    exact ⟨hρ j, Finsupp.single j 1, by rw [coverSecondBoundary_single, one_smul]⟩
  exact ((Subgroup.normalClosure_le_normal hrange) hw).2

/-- Every finite two-boundary is the Fox vector of a consequence of the relators. -/
theorem exists_mem_normalClosure_of_coverSecondBoundary (hρ : ∀ j, ρ j ∈ N)
    (c : J →₀ CoverRing N) :
    ∃ w ∈ Subgroup.normalClosure (Set.range ρ),
      coverSecondBoundary N ρ c = coverFoxGradient N w := by
  classical
  have hRle : Subgroup.normalClosure (Set.range ρ) ≤ N := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨j, rfl⟩
    exact hρ j
  induction c using Finsupp.induction_linear with
  | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
  | add c d hc hd =>
      obtain ⟨v, hv, he⟩ := hc
      obtain ⟨w, hw, hf⟩ := hd
      exact ⟨v * w, Subgroup.mul_mem _ hv hw, by
        rw [map_add, he, hf, coverFoxGradient_mul N (hRle hv)]⟩
  | single j x =>
      obtain ⟨w, hw, he⟩ := exists_mem_smul_foxVec hRle
        (Subgroup.subset_normalClosure (Set.mem_range_self j)) x
      refine ⟨w, hw, ?_⟩
      rw [coverSecondBoundary_single]
      apply Finsupp.ext
      intro i
      exact congrFun he i

/-- The integral Hurewicz membership calculation for arbitrary presentations. -/
theorem coverFoxGradient_mem_range_iff (hρ : ∀ j, ρ j ∈ N)
    {w : FreeGroup α} (hw : w ∈ N) :
    (∃ c : J →₀ CoverRing N, coverSecondBoundary N ρ c = coverFoxGradient N w) ↔
      w ∈ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆ := by
  have hRle : Subgroup.normalClosure (Set.range ρ) ≤ N := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨j, rfl⟩
    exact hρ j
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨r, hr, he⟩ := exists_mem_normalClosure_of_coverSecondBoundary N ρ hρ c
    have hh : coverFoxGradient N (w * r⁻¹) = 0 := by
      rw [coverFoxGradient_mul N hw, coverFoxGradient_inv N (hRle hr), ← hc, ← he]
      exact add_neg_cancel _
    have hm := (coverFoxGradient_eq_zero_iff N (N.mul_mem hw (N.inv_mem (hRle hr)))).mp hh
    have hw' : w = (w * r⁻¹) * r := by group
    rw [hw']
    exact Subgroup.mul_mem _
      ((le_sup_right : ⁅N, N⁆ ≤ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆) hm)
      ((le_sup_left : Subgroup.normalClosure (Set.range ρ) ≤
        Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆) hr)
  · intro hw'
    obtain ⟨r, hr, t, ht, he⟩ := Subgroup.mem_sup_of_normal_right.mp hw'
    obtain ⟨c, hc⟩ := exists_coverSecondBoundary_of_mem_normalClosure N ρ hρ hr
    refine ⟨c, ?_⟩
    rw [← he, coverFoxGradient_mul N (hRle hr),
      (coverFoxGradient_eq_zero_iff N (Subgroup.commutator_le_left N N ht)).mpr ht, add_zero]
    exact hc

/-- Perfectness of the quotient covering subgroup gives exactness in degree one,
without any finite-presentation restriction. -/
theorem exists_coverSecondBoundary_preimage (hρ : ∀ j, ρ j ∈ N)
    (hperfect : N ≤ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆)
    (c : α →₀ CoverRing N) (hc : coverFirstBoundary N c = 0) :
    ∃ d : J →₀ CoverRing N, coverSecondBoundary N ρ d = c := by
  obtain ⟨w, hw, rfl⟩ := exists_mem_of_coverFirstBoundary_eq_zero N c hc
  exact (coverFoxGradient_mem_range_iff N ρ hρ hw).mpr (hperfect hw)

end FiniteChains
