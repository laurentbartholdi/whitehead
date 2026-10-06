import RequestProject.HomeomorphContinuousMap
import RequestProject.SquareBoundaryNormHomeomorph
import Mathlib.Analysis.Convex.StdSimplex

/-! Explicit disk coordinates for strict order triangles. The bottom
edge of the square is collapsed to vertex 0, while its other three sides
read edges 01, 12, and 02. The map is a quotient on the closed disk and a
homeomorphism on interiors. No orientation of the previously chosen
convex-simplex homeomorphism is assumed. Pending final Lean verification. -/

noncomputable section
open scoped Classical unitInterval Topology
namespace FiniteChains.OrderTriangleDisk
open RelativeAttachment Topology

abbrev Triangle := stdSimplex ℝ (Fin 3)
abbrev Square := Fin 2 → I

def parametrization : C(Square, Triangle) where
  toFun z := ⟨![1 - (z 1 : ℝ), (z 1 : ℝ) * (1 - (z 0 : ℝ)),
      (z 1 : ℝ) * (z 0 : ℝ)], by
    constructor
    · intro i
      fin_cases i
      · exact sub_nonneg.mpr (z 1).property.2
      · exact mul_nonneg (z 1).property.1 (sub_nonneg.mpr (z 0).property.2)
      · exact mul_nonneg (z 1).property.1 (z 0).property.1
    · rw [Fin.sum_univ_three]
      dsimp
      ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

theorem coordinate_sum (z : Triangle) : z.val 0 + z.val 1 + z.val 2 = 1 :=
  (Fin.sum_univ_three z.val).symm.trans z.property.2

theorem remaining_nonneg (z : Triangle) : 0 ≤ 1 - z.val 0 := by
  have hs := coordinate_sum z
  linarith [z.property.1 1, z.property.1 2]

theorem remaining_zero (z : Triangle) (h : 1 - z.val 0 = 0) :
    z.val 1 = 0 ∧ z.val 2 = 0 := by
  have hs := coordinate_sum z
  constructor <;> linarith [z.property.1 1, z.property.1 2]

def sectionPoint (z : Triangle) : Square :=
  ![⟨z.val 2 / (1 - z.val 0), by
      constructor
      · exact div_nonneg (z.property.1 2) (remaining_nonneg z)
      · by_cases h : 1 - z.val 0 = 0
        · simp [h]
        · apply (div_le_one (lt_of_le_of_ne (remaining_nonneg z) (Ne.symm h))).mpr
          have hs := coordinate_sum z
          linarith [z.property.1 1]⟩,
    ⟨1 - z.val 0, remaining_nonneg z, by linarith [z.property.1 0]⟩]

theorem parametrization_section (z : Triangle) : parametrization (sectionPoint z) = z := by
  apply Subtype.ext
  funext i
  have hs := coordinate_sum z
  by_cases h : 1 - z.val 0 = 0
  · obtain ⟨h₁, h₂⟩ := remaining_zero z h
    fin_cases i <;> simp [parametrization, sectionPoint, h, h₁, h₂]
    linarith
  · fin_cases i
    · change 1 - (1 - z.val 0) = z.val 0
      ring
    · change (1 - z.val 0) * (1 - z.val 2 / (1 - z.val 0)) = z.val 1
      rw [mul_sub, mul_one, mul_div_cancel₀ _ h]
      linarith
    · change (1 - z.val 0) * (z.val 2 / (1 - z.val 0)) = z.val 2
      exact mul_div_cancel₀ _ h

theorem parametrization_surjective : Function.Surjective parametrization :=
  fun z => ⟨sectionPoint z, parametrization_section z⟩

theorem parametrization_isQuotientMap : IsQuotientMap parametrization :=
  parametrization.continuous.isClosedMap.isQuotientMap
    parametrization.continuous parametrization_surjective

def SquareInterior (z : Square) : Prop := ∀ i, 0 < (z i : ℝ) ∧ (z i : ℝ) < 1

theorem parametrization_positive_iff (z : Square) :
    (∀ i, 0 < (parametrization z).val i) ↔ SquareInterior z := by
  constructor
  · intro h
    have h₀ : 0 < 1 - (z 1 : ℝ) := h 0
    have h₁ : 0 < (z 1 : ℝ) * (1 - (z 0 : ℝ)) := h 1
    have h₂ : 0 < (z 1 : ℝ) * (z 0 : ℝ) := h 2
    have hxy : 0 < (z 1 : ℝ) ∧ 0 < (z 0 : ℝ) :=
      (mul_pos_iff.mp h₂).resolve_right
        (fun hneg => (not_lt_of_ge (z 1).property.1) hneg.1)
    have hy := hxy.1
    have hx := hxy.2
    have hx' : 0 < 1 - (z 0 : ℝ) := (mul_pos_iff_of_pos_left hy).mp h₁
    intro i
    fin_cases i <;> dsimp <;> constructor <;> linarith
  · intro h i
    fin_cases i
    · exact sub_pos.mpr (h 1).2
    · exact mul_pos (h 1).1 (sub_pos.mpr (h 0).2)
    · exact mul_pos (h 1).1 (h 0).1

theorem parametrization_injective_off_collapsed_side {z w : Square}
    (hz : (z 1 : ℝ) ≠ 0) (h : parametrization z = parametrization w) : z = w := by
  have hy : (z 1 : ℝ) = (w 1 : ℝ) := by
    have he := congrArg (fun t : Triangle => t.val 0) h
    change 1 - (z 1 : ℝ) = 1 - (w 1 : ℝ) at he
    linarith
  have hx : (z 0 : ℝ) = (w 0 : ℝ) := by
    have he := congrArg (fun t : Triangle => t.val 2) h
    change (z 1 : ℝ) * (z 0 : ℝ) = (w 1 : ℝ) * (w 0 : ℝ) at he
    rw [← hy] at he
    exact (mul_left_cancel₀ hz) he
  funext i
  apply Subtype.ext
  fin_cases i
  · exact hx
  · exact hy

theorem sectionPoint_interior (z : {z : Triangle // ∀ i, 0 < z.val i}) :
    SquareInterior (sectionPoint z.val) :=
  (parametrization_positive_iff _).mp (by
    rw [parametrization_section]
    exact z.property)

def interiorHomeomorph :
    {z : Square // SquareInterior z} ≃ₜ {z : Triangle // ∀ i, 0 < z.val i} where
  toFun z := ⟨parametrization z.val, (parametrization_positive_iff z.val).mpr z.property⟩
  invFun z := ⟨sectionPoint z.val, sectionPoint_interior z⟩
  left_inv z := by
    apply Subtype.ext
    exact parametrization_injective_off_collapsed_side
      (ne_of_gt ((sectionPoint_interior ⟨parametrization z.val,
        (parametrization_positive_iff z.val).mpr z.property⟩) 1).1)
      (parametrization_section (parametrization z.val))
  right_inv z := Subtype.ext (parametrization_section z.val)
  continuous_toFun := (parametrization.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    have hc (i : Fin 3) : Continuous
        (fun z : {z : Triangle // ∀ i, 0 < z.val i} => z.val.val i) :=
      (continuous_apply i).comp (continuous_subtype_val.comp continuous_subtype_val)
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · apply Continuous.subtype_mk
      apply Continuous.div
      · exact hc 2
      · exact continuous_const.sub (hc 0)
      · intro z
        have hs := coordinate_sum z.val
        have hp := z.property 1
        have hq := z.property 2
        linarith
    · apply Continuous.subtype_mk
      exact continuous_const.sub (hc 0)

def squareBallHomeomorph : ClosedUnitBall (Fin 2 → ℝ) ≃ₜ Square where
  toFun x i := ⟨(x.val i + 1) / 2, by
    have hi : |x.val i| ≤ 1 := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x.val i).trans x.property
    obtain ⟨hl, hu⟩ := abs_le.mp hi
    constructor <;> linarith⟩
  invFun z := ⟨fun i => 2 * (z i : ℝ) - 1, by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    have hi := (z i).property
    constructor <;> linarith [hi.1, hi.2]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    dsimp
    ring
  right_inv z := by
    funext i
    apply Subtype.ext
    dsimp
    ring
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    exact (((continuous_apply i).comp continuous_subtype_val).add continuous_const).div_const 2
  continuous_invFun := by fun_prop

theorem squareBallHomeomorph_interior (x : ClosedUnitBall (Fin 2 → ℝ)) :
    SquareInterior (squareBallHomeomorph x) ↔ ‖x.val‖ < 1 := by
  rw [pi_norm_lt_iff zero_lt_one]
  constructor
  · intro h i
    have hi := h i
    rw [Real.norm_eq_abs]
    apply abs_lt.mpr
    change 0 < (x.val i + 1) / 2 ∧ (x.val i + 1) / 2 < 1 at hi
    constructor <;> linarith [hi.1, hi.2]
  · intro h i
    have hi := abs_lt.mp (by simpa only [Real.norm_eq_abs] using h i)
    change 0 < (x.val i + 1) / 2 ∧ (x.val i + 1) / 2 < 1
    constructor <;> linarith [hi.1, hi.2]

theorem squareBallHomeomorph_boundary (z : UnitBoundary (Fin 2 → ℝ)) :
    squareBallHomeomorph (unitBoundaryInclusion _ z) =
      (unitBoundarySquareHomeomorph z).val := rfl

def disk : C(ClosedUnitBall (Fin 2 → ℝ), Triangle) :=
  parametrization.comp squareBallHomeomorph.toContinuousMap

theorem disk_positive_iff (x : ClosedUnitBall (Fin 2 → ℝ)) :
    (∀ i, 0 < (disk x).val i) ↔ ‖x.val‖ < 1 :=
  (parametrization_positive_iff _).trans (squareBallHomeomorph_interior x)

theorem disk_isQuotientMap : IsQuotientMap disk :=
  parametrization_isQuotientMap.comp squareBallHomeomorph.isQuotientMap

theorem disk_injOn_interior : Set.InjOn disk {x | ‖x.val‖ < 1} := by
  intro x hx y _ h
  apply squareBallHomeomorph.injective
  exact parametrization_injective_off_collapsed_side
    (ne_of_gt (((squareBallHomeomorph_interior x).mpr hx) 1).1) h

theorem side_left (t : I) :
    (parametrization (squareSideMap (0, false) t).val).val =
      ![1 - (t : ℝ), (t : ℝ), 0] := by
  funext i
  fin_cases i <;> simp [parametrization, squareSideMap, Whitehead.squareEdge, boolEndpoint]

theorem side_top (t : I) :
    (parametrization (squareSideMap (1, true) t).val).val =
      ![0, 1 - (t : ℝ), (t : ℝ)] := by
  funext i
  fin_cases i <;> simp [parametrization, squareSideMap, Whitehead.squareEdge, boolEndpoint]

theorem side_right (t : I) :
    (parametrization (squareSideMap (0, true) t).val).val =
      ![1 - (t : ℝ), 0, (t : ℝ)] := by
  funext i
  fin_cases i <;> simp [parametrization, squareSideMap, Whitehead.squareEdge, boolEndpoint]

theorem side_bottom (t : I) :
    (parametrization (squareSideMap (1, false) t).val).val = ![1, 0, 0] := by
  funext i
  fin_cases i <;> simp [parametrization, squareSideMap, Whitehead.squareEdge, boolEndpoint]

end FiniteChains.OrderTriangleDisk
