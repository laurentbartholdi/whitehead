import RequestProject.NecessityLocallyFinite
import RequestProject.CoverChainComplex

/-! Finitely supported Fox calculus for arbitrary generator sets. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

variable {α : Type*} [DecidableEq α]

noncomputable def foxGradient (w : FreeGroup α) : α →₀ FreeGroupRing α :=
  Finsupp.ofSupportFinite (fun i => fox i w) (fox_generator_support_finite w)

@[simp] theorem foxGradient_apply (w : FreeGroup α) (i : α) :
    foxGradient w i = fox i w := rfl

@[simp] theorem foxGradient_one : foxGradient (1 : FreeGroup α) = 0 := by
  ext i
  simp

@[simp] theorem foxGradient_of (i : α) :
    foxGradient (FreeGroup.of i) = Finsupp.single i 1 := by
  ext j
  simp [fox_of, Finsupp.single_apply, eq_comm]

theorem foxGradient_mul (a b : FreeGroup α) :
    foxGradient (a * b) = foxGradient a + grp a • foxGradient b := by
  ext i
  simp [fox_mul]

theorem foxGradient_inv (a : FreeGroup α) :
    foxGradient a⁻¹ = -(grp a⁻¹ • foxGradient a) := by
  ext i
  simp [fox_inv]

noncomputable def freeFirstBoundary :
    (α →₀ FreeGroupRing α) →ₗ[FreeGroupRing α] FreeGroupRing α :=
  Finsupp.linearCombination _ (fun i => grp (FreeGroup.of i) - 1)

/-- The fundamental Fox identity without a finite-generator hypothesis. -/
theorem fox_fundamental_finsupp (w : FreeGroup α) :
    freeFirstBoundary (foxGradient w) = grp w - 1 := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of k => simp [freeFirstBoundary]
  | inv_of k hk =>
      rw [foxGradient_inv, map_neg, map_smul, hk]
      change -(grp (FreeGroup.of k)⁻¹ * (grp (FreeGroup.of k) - 1)) = _
      rw [mul_sub, grp_inv_mul_grp, mul_one]
      noncomm_ring
  | mul a b ha hb =>
      rw [foxGradient_mul, map_add, map_smul, ha, hb, grp_mul]
      change (grp a - 1) + grp a * (grp b - 1) = _
      noncomm_ring

variable (N : Subgroup (FreeGroup α)) [N.Normal]

noncomputable def coverFoxGradient (w : FreeGroup α) : α →₀ CoverRing N :=
  (foxGradient w).mapRange (proj N) (map_zero _)

noncomputable def coverFirstBoundary :
    (α →₀ CoverRing N) →ₗ[CoverRing N] CoverRing N :=
  Finsupp.linearCombination _ (fun i => qgrp N (FreeGroup.of i) - 1)

omit [DecidableEq α] in
/-- Projection of the group ring commutes with the finitely supported first boundary. -/
theorem coverFirstBoundary_mapRange (c : α →₀ FreeGroupRing α) :
    coverFirstBoundary N (c.mapRange (proj N) (map_zero _)) =
      proj N (freeFirstBoundary c) := by
  simp only [coverFirstBoundary, freeFirstBoundary, Finsupp.linearCombination_apply,
    smul_eq_mul]
  rw [Finsupp.sum_mapRange_index (fun i => zero_mul _), map_finsuppSum]
  apply Finsupp.sum_congr
  intro i ci
  simp only [map_mul, map_sub, map_one, proj_grp]

theorem coverFirstBoundary_gradient (w : FreeGroup α) :
    coverFirstBoundary N (coverFoxGradient N w) = qgrp N w - 1 := by
  rw [coverFoxGradient, coverFirstBoundary_mapRange, fox_fundamental_finsupp,
    map_sub, proj_grp, map_one]

theorem coverFoxGradient_isCycle {w : FreeGroup α} (hw : w ∈ N) :
    coverFirstBoundary N (coverFoxGradient N w) = 0 := by
  rw [coverFirstBoundary_gradient, qgrp_eq_one_of_mem N hw, sub_self]

noncomputable def coverSecondBoundary {J : Type*} (ρ : J → FreeGroup α) :
    (J →₀ CoverRing N) →ₗ[CoverRing N] (α →₀ CoverRing N) :=
  Finsupp.linearCombination _ (fun j => coverFoxGradient N (ρ j))

/-- The finitely supported cover boundaries form a chain complex, with no finite-cell
assumptions on either the generators or relators. -/
theorem coverFirstBoundary_coverSecondBoundary {J : Type*} (ρ : J → FreeGroup α)
    (hρ : ∀ j, ρ j ∈ N) (c : J →₀ CoverRing N) :
    coverFirstBoundary N (coverSecondBoundary N ρ c) = 0 := by
  rw [coverSecondBoundary, Finsupp.linearCombination_apply, map_finsuppSum]
  change ∑ j ∈ c.support, coverFirstBoundary N (c j • coverFoxGradient N (ρ j)) = 0
  apply Finset.sum_eq_zero
  intro j hj
  rw [map_smul, coverFoxGradient_isCycle N (hρ j), smul_zero]

noncomputable def linearFoxGradient :
    FreeGroupRing α →ₗ[ℤ] (α →₀ FreeGroupRing α) :=
  (Finsupp.linearCombination ℤ (fun g => foxGradient g)).comp (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

@[simp] theorem linearFoxGradient_single (g : FreeGroup α) (n : ℤ) :
    linearFoxGradient (MonoidAlgebra.single g n) = n • foxGradient g :=
  by
    change Finsupp.linearCombination ℤ (fun g => foxGradient g) (Finsupp.single g n) = _
    exact Finsupp.linearCombination_single ℤ n g

theorem linearFoxGradient_fundamental (a : FreeGroupRing α) :
    freeFirstBoundary (linearFoxGradient a) = a - aug a • 1 := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
      rw [map_add, map_add, ha, hb, map_add, add_smul]
      abel
  | single g n =>
      rw [linearFoxGradient_single, map_zsmul, fox_fundamental_finsupp,
        aug_single, single_eq_smul_grp, smul_sub]

/-- The augmentation ideal is the image of the first boundary for arbitrary generator sets. -/
theorem exists_coverFirstBoundary_preimage (z : CoverRing N) (hz : augQ N z = 0) :
    ∃ c : α →₀ CoverRing N, coverFirstBoundary N c = z := by
  refine ⟨(linearFoxGradient (liftQ N z)).mapRange (proj N) (map_zero _), ?_⟩
  have haug : aug (liftQ N z) = 0 := by
    rw [← augQ_proj N, proj_liftQ, hz]
  rw [coverFirstBoundary_mapRange, linearFoxGradient_fundamental,
    haug, zero_smul, sub_zero, proj_liftQ]

end FiniteChains
