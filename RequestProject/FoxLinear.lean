import RequestProject.Fox

/-!
# The Fox derivative as a linear map on the group ring

`RequestProject/Fox.lean` constructs the Fox derivative `∂w/∂x_i` of a word `w` of the free
group.  For the chain complex of a covering complex one needs its linear extension

`D_i : ℤ[F] → ℤ[F]`,  `D_i (∑ n_g g) = ∑ n_g ∂g/∂x_i`,

which satisfies the Leibniz rule `D_i (a b) = ε(b) • D_i a + a · D_i b` (here `ε` is the
augmentation) and the fundamental identity `∑_i D_i(a) (x_i - 1) = a - ε(a)`.

These two facts are the algebraic engine behind the identification of the cellular chain
complex of the cover `K_N` (Remark 1 of the paper) and behind the exactness statements
proved in `RequestProject/CoverChainComplex.lean`.
-/

namespace FiniteChains

open MonoidAlgebra

variable {α : Type*} [DecidableEq α]

/-- The linear extension `D_i : ℤ[F] → ℤ[F]` of the Fox derivative `∂/∂x_i`. -/
noncomputable def foxLin (i : α) : FreeGroupRing α →ₗ[ℤ] FreeGroupRing α :=
  (Finsupp.linearCombination ℤ (fun g => fox i g)).comp
    (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

@[simp] theorem foxLin_single (i : α) (g : FreeGroup α) (n : ℤ) :
    foxLin i (single g n) = n • fox i g :=
  by
    change Finsupp.linearCombination ℤ (fun g => fox i g) (Finsupp.single g n) = _
    exact Finsupp.linearCombination_single ℤ n g

omit [DecidableEq α] in
theorem grp_eq_single (g : FreeGroup α) : (grp g : FreeGroupRing α) = single g 1 := rfl

@[simp] theorem foxLin_grp (i : α) (g : FreeGroup α) : foxLin i (grp g) = fox i g := by
  rw [grp_eq_single, foxLin_single, one_smul]

omit [DecidableEq α] in
theorem single_eq_smul_grp (g : FreeGroup α) (n : ℤ) :
    (single g n : FreeGroupRing α) = n • grp g := by
  rw [grp_eq_single, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]

omit [DecidableEq α] in
@[simp] theorem aug_single (g : FreeGroup α) (n : ℤ) :
    aug (single g n : FreeGroupRing α) = n := by
  rw [single_eq_smul_grp, map_zsmul, aug_grp, smul_eq_mul, mul_one]

/-- The Leibniz rule for the linear extension of the Fox derivative. -/
theorem foxLin_mul (i : α) (a b : FreeGroupRing α) :
    foxLin i (a * b) = aug b • foxLin i a + a * foxLin i b := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a₁ a₂ h₁ h₂ =>
      rw [add_mul, map_add, h₁, h₂, map_add, smul_add, add_mul]
      abel
  | single g n =>
      induction b using MonoidAlgebra.induction_linear with
      | zero => simp
      | add b₁ b₂ h₁ h₂ =>
          rw [mul_add, map_add, h₁, h₂, map_add, map_add, add_smul, mul_add]
          abel
      | single h m =>
          rw [MonoidAlgebra.single_mul_single, foxLin_single, foxLin_single, foxLin_single,
            aug_single, fox_mul, single_eq_smul_grp g n, smul_mul_assoc, smul_smul]
          simp only [smul_add, zsmul_eq_mul, Int.cast_mul, mul_assoc]
          rw [← mul_assoc (m : FreeGroupRing α), (Int.cast_commute m (grp g)).eq, mul_assoc]
          congr 1
          rw [← mul_assoc, ← mul_assoc, ← Int.cast_mul, ← Int.cast_mul, mul_comm n m]

/-- The fundamental identity of the free differential calculus, linearly extended. -/
theorem foxLin_fundamental [Fintype α] (a : FreeGroupRing α) :
    ∑ i : α, foxLin i a * (grp (FreeGroup.of i) - 1) = a - (aug a) • 1 := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a₁ a₂ h₁ h₂ =>
      have hstep : ∀ i : α, foxLin i (a₁ + a₂) * (grp (FreeGroup.of i) - 1)
          = foxLin i a₁ * (grp (FreeGroup.of i) - 1)
            + foxLin i a₂ * (grp (FreeGroup.of i) - 1) := by
        intro i; rw [map_add, add_mul]
      rw [Finset.sum_congr rfl (fun i _ => hstep i), Finset.sum_add_distrib, h₁, h₂, map_add,
        add_smul, sub_add_sub_comm]
  | single g n =>
      have hstep : ∀ i : α, foxLin i (single g n) * (grp (FreeGroup.of i) - 1)
          = n • (fox i g * (grp (FreeGroup.of i) - 1)) := by
        intro i; rw [foxLin_single, smul_mul_assoc]
      rw [Finset.sum_congr rfl (fun i _ => hstep i), ← Finset.smul_sum, fox_fundamental,
        aug_single, single_eq_smul_grp, smul_sub]

end FiniteChains
