module

public import RequestProject.AttachmentHomotopyExtension
public import Mathlib.Analysis.Normed.Group.Constructions

@[expose] public section

/-! Homotopy extension on the entire boundary of `I × D`, including both
ends. The cylinder is the unit ball for the product supremum norm. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u
variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev FullBallCylinderBoundary :=
  {z : I × ClosedUnitBall E // z.1 = 0 ∨ z.1 = 1 ∨ ‖z.2.val‖ = 1}

def ballCylinderForward (z : ClosedUnitBall (ℝ × E)) : I × ClosedUnitBall E :=
  (⟨(z.val.1 + 1) / 2, by
    have h : |z.val.1| ≤ 1 := by
      simpa only [Real.norm_eq_abs] using (norm_fst_le z.val).trans z.property
    obtain ⟨hl, hu⟩ := abs_le.mp h
    constructor <;> linarith⟩,
   ⟨z.val.2, (norm_snd_le z.val).trans z.property⟩)

def ballCylinderInverse (z : I × ClosedUnitBall E) : ClosedUnitBall (ℝ × E) :=
  ⟨(2 * (z.1 : ℝ) - 1, z.2.val), by
    rw [Prod.norm_mk, Real.norm_eq_abs]
    apply max_le _ z.2.property
    rw [abs_le]
    have hl := z.1.2.1
    have hu := z.1.2.2
    constructor <;> linarith⟩

/-- The cylinder is literally a ball in the product norm, after rescaling
its interval coordinate from `[-1,1]` to `[0,1]`. -/
def ballCylinderHomeomorph : ClosedUnitBall (ℝ × E) ≃ₜ I × ClosedUnitBall E where
  toFun := ballCylinderForward E
  invFun := ballCylinderInverse E
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · change 2 * ((z.val.1 + 1) / 2) - 1 = z.val.1
      ring
    · rfl
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      change ((2 * (z.1 : ℝ) - 1) + 1) / 2 = (z.1 : ℝ)
      ring
    · rfl
  continuous_toFun := by
    unfold ballCylinderForward
    fun_prop
  continuous_invFun := by
    unfold ballCylinderInverse
    fun_prop

omit [NormedSpace ℝ E] in
theorem ballCylinderForward_boundary (z : UnitBoundary (ℝ × E)) :
    (ballCylinderHomeomorph E (unitBoundaryInclusion (ℝ × E) z)).1 = 0 ∨
    (ballCylinderHomeomorph E (unitBoundaryInclusion (ℝ × E) z)).1 = 1 ∨
    ‖(ballCylinderHomeomorph E (unitBoundaryInclusion (ℝ × E) z)).2.val‖ = 1 := by
  have he : max |z.val.1| ‖z.val.2‖ = 1 := by
    have hz := z.property
    change ‖(z.val : ℝ × E)‖ = 1 at hz
    rw [Prod.norm_mk, Real.norm_eq_abs] at hz
    exact hz
  by_cases hs : ‖z.val.2‖ = 1
  · exact Or.inr (Or.inr hs)
  have hf : |z.val.1| = 1 := by
    by_cases hle : |z.val.1| ≤ ‖z.val.2‖
    · rw [max_eq_right hle] at he
      exact (hs he).elim
    · simpa only [max_eq_left (le_of_not_ge hle)] using he
  by_cases hz : 0 ≤ z.val.1
  · right
    left
    apply Subtype.ext
    change (z.val.1 + 1) / 2 = (1 : ℝ)
    rw [abs_of_nonneg hz] at hf
    linarith
  · left
    apply Subtype.ext
    change (z.val.1 + 1) / 2 = (0 : ℝ)
    rw [abs_of_nonpos (le_of_not_ge hz)] at hf
    linarith

omit [NormedSpace ℝ E] in
theorem ballCylinderInverse_boundary (z : FullBallCylinderBoundary E) :
    ‖((ballCylinderHomeomorph E).symm z.val).val‖ = 1 := by
  apply le_antisymm ((ballCylinderHomeomorph E).symm z.val).property
  change 1 ≤ max ‖2 * (z.val.1 : ℝ) - 1‖ ‖z.val.2.val‖
  rcases z.property with hz | hz | hz
  · have ht : ‖2 * (z.val.1 : ℝ) - 1‖ = 1 := by norm_num [hz]
    rw [ht]
    exact le_max_left _ _
  · have ht : ‖2 * (z.val.1 : ℝ) - 1‖ = 1 := by norm_num [hz]
    rw [ht]
    exact le_max_left _ _
  · rw [hz]
    exact le_max_right _ _

/-- The sphere for the product norm is exactly the union of the two ends
and the side boundary of the disk cylinder. -/
def ballCylinderBoundaryHomeomorph : UnitBoundary (ℝ × E) ≃ₜ FullBallCylinderBoundary E where
  toFun z := ⟨ballCylinderHomeomorph E (unitBoundaryInclusion (ℝ × E) z),
    ballCylinderForward_boundary E z⟩
  invFun z := ⟨((ballCylinderHomeomorph E).symm z.val).val,
    ballCylinderInverse_boundary E z⟩
  left_inv z := by
    apply Subtype.ext
    exact congrArg (fun w : ClosedUnitBall (ℝ × E) => w.val)
      ((ballCylinderHomeomorph E).symm_apply_apply
      (unitBoundaryInclusion (ℝ × E) z))
  right_inv z := by
    apply Subtype.ext
    exact (ballCylinderHomeomorph E).apply_symm_apply z.val
  continuous_toFun :=
    ((ballCylinderHomeomorph E).continuous.comp
      (unitBoundaryInclusion (ℝ × E)).continuous).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp
      ((ballCylinderHomeomorph E).symm.continuous.comp continuous_subtype_val)).subtype_mk _

/-- Relative homotopy extension that also keeps both endpoint disk maps
fixed. This is the geometric input for cancelling a boundary backtrack. -/
theorem fullBallCylinderBoundary_hasHomotopyExtension :
    HasHomotopyExtension (Subtype.val : FullBallCylinderBoundary E → I × ClosedUnitBall E) :=
  (unitBoundary_hasHomotopyExtension (ℝ × E)).homeomorph
    (ballCylinderBoundaryHomeomorph E) (ballCylinderHomeomorph E) Subtype.val
    (fun _ => rfl)

end FiniteChains.RelativeAttachment
