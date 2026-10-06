import RequestProject.SquareSideQuotient
import RequestProject.ClassicalCWOneCellCellularization

/-! Affine coordinates identify the actual sup-norm disk boundary with
the square boundary, and the one-dimensional disk with the unit interval. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open scoped Topology unitInterval Classical

private theorem norm_coordinate_bounds {n : ℕ} (x : Fin n → ℝ)
    (hx : ‖x‖ ≤ 1) (i : Fin n) : -1 ≤ x i ∧ x i ≤ 1 := by
  have hi : |x i| ≤ 1 := (Real.norm_eq_abs (x i)) ▸ (norm_le_pi_norm x i).trans hx
  exact abs_le.mp hi

private theorem norm_one_coordinate {n : ℕ} (x : Fin n → ℝ) (hx : ‖x‖ = 1) :
    ∃ i, x i = 1 ∨ x i = -1 := by
  by_contra! h
  have hl : ‖x‖ < 1 := (pi_norm_lt_iff zero_lt_one).mpr (fun i => by
    have hu : ‖x i‖ ≤ 1 := (norm_le_pi_norm x i).trans hx.le
    apply lt_of_le_of_ne hu
    intro he
    have hi : x i = 1 ∨ x i = -1 := (abs_eq zero_le_one).mp
      (by simpa only [Real.norm_eq_abs] using he)
    exact hi.elim (h i).1 (h i).2)
  exact (not_lt_of_ge hx.ge) hl

def unitBoundarySquareHomeomorph : UnitBoundary (Fin 2 → ℝ) ≃ₜ SquareBoundary where
  toFun x := ⟨fun i => ⟨(x.val i + 1) / 2, by
      have hi := norm_coordinate_bounds x.val x.property.le i
      constructor <;> linarith⟩, by
    obtain ⟨i, hi | hi⟩ := norm_one_coordinate x.val x.property
    · exact ⟨i, Or.inr (Subtype.ext (by simp [hi]))⟩
    · exact ⟨i, Or.inl (Subtype.ext (by simp [hi]))⟩⟩
  invFun x := ⟨fun i => 2 * (x.val i : ℝ) - 1, by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro i
      rw [Real.norm_eq_abs]
      apply abs_le.mpr
      have hi := (x.val i).property
      constructor <;> linarith [hi.1, hi.2]
    · obtain ⟨i, hi | hi⟩ := x.property
      · have h := norm_le_pi_norm (fun j => 2 * (x.val j : ℝ) - 1) i
        simpa only [hi, Set.Icc.coe_zero, mul_zero, zero_sub, norm_neg, norm_one] using h
      · have h := norm_le_pi_norm (fun j => 2 * (x.val j : ℝ) - 1) i
        norm_num only [hi, Set.Icc.coe_one, mul_one, show (2 : ℝ) - 1 = 1 by norm_num,
          norm_one] at h
        exact h⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    dsimp
    ring
  right_inv x := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    dsimp
    ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    exact (((continuous_apply i).comp continuous_subtype_val).add continuous_const).div_const 2
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_const.mul
      (continuous_subtype_val.comp ((continuous_apply i).comp continuous_subtype_val))).sub
        continuous_const

def oneBallIntervalHomeomorph : ClosedUnitBall (Fin 1 → ℝ) ≃ₜ I where
  toFun x := ⟨(x.val 0 + 1) / 2, by
    have hi := norm_coordinate_bounds x.val x.property 0
    constructor <;> linarith⟩
  invFun t := ⟨fun _ => 2 * (t : ℝ) - 1, by
    rw [pi_norm_const, Real.norm_eq_abs]
    apply abs_le.mpr
    have ht := t.property
    constructor <;> linarith [ht.1, ht.2]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    dsimp
    ring
  right_inv t := by
    apply Subtype.ext
    dsimp
    ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (((continuous_apply 0).comp continuous_subtype_val).add continuous_const).div_const 2
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun _ =>
      (continuous_const.mul continuous_subtype_val).sub continuous_const

def oneBoundaryPoint (b : Bool) : UnitBoundary (Fin 1 → ℝ) :=
  ⟨fun _ => if b then 1 else -1, by cases b <;> simp [pi_norm_const]⟩

theorem oneBoundary_eq (a : UnitBoundary (Fin 1 → ℝ)) :
    a = oneBoundaryPoint false ∨ a = oneBoundaryPoint true := by
  obtain ⟨i, hi | hi⟩ := norm_one_coordinate a.val a.property
  · apply Or.inr
    apply Subtype.ext
    funext j
    have hj : j = i := Subsingleton.elim _ _
    simpa [hj, oneBoundaryPoint] using hi
  · apply Or.inl
    apply Subtype.ext
    funext j
    have hj : j = i := Subsingleton.elim _ _
    simpa [hj, oneBoundaryPoint] using hi

@[simp] theorem oneBallIntervalHomeomorph_boundary (b : Bool) :
    oneBallIntervalHomeomorph (unitBoundaryInclusion _ (oneBoundaryPoint b)) =
      boolEndpoint b := by
  apply Subtype.ext
  cases b <;> norm_num [oneBallIntervalHomeomorph, unitBoundaryInclusion,
    oneBoundaryPoint, boolEndpoint]

end FiniteChains.RelativeAttachment
