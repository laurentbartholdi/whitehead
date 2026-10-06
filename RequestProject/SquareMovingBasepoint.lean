import RequestProject.HomeomorphContinuousMap
import RequestProject.TopologicalCoverPi2
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Tactic

/-! A moving constant boundary can be made stationary by an explicit square collar.
The construction uses no local contractibility or cofibration hypothesis on the target. -/

noncomputable section

namespace Whitehead
open scoped unitInterval Topology

private abbrev Square := Fin 2 → I

private def squareOrigin : Square := fun _ => 0

private theorem squareOrigin_boundary : squareOrigin ∈ Cube.boundary (Fin 2) :=
  ⟨0, Or.inl rfl⟩

/-- Distance from the nearest face of the square, in its standard coordinates. -/
private def squareDepth (z : Square) : ℝ :=
  min (min (z 0 : ℝ) (1 - z 0)) (min (z 1 : ℝ) (1 - z 1))

private theorem squareDepth_nonneg (z : Square) : 0 ≤ squareDepth z := by
  exact le_min (le_min (z 0).2.1 (sub_nonneg.mpr (z 0).2.2))
    (le_min (z 1).2.1 (sub_nonneg.mpr (z 1).2.2))

private theorem squareDepth_le_coordinate (z : Square) (i : Fin 2) :
    squareDepth z ≤ (z i : ℝ) := by
  fin_cases i
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_left _ _)

private theorem squareDepth_le_complement (z : Square) (i : Fin 2) :
    squareDepth z ≤ 1 - (z i : ℝ) := by
  fin_cases i
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

private theorem squareDepth_boundary (z : Square) (hz : z ∈ Cube.boundary (Fin 2)) :
    squareDepth z = 0 := by
  apply le_antisymm _ (squareDepth_nonneg z)
  obtain ⟨i, hi | hi⟩ := hz
  · simpa only [hi, Set.Icc.coe_zero] using squareDepth_le_coordinate z i
  · simpa only [hi, Set.Icc.coe_one, sub_self] using squareDepth_le_complement z i

private theorem squareDepth_coordinate (z : Square) :
    ∃ i : Fin 2, squareDepth z = (z i : ℝ) ∨ squareDepth z = 1 - (z i : ℝ) := by
  have hmin (a b : ℝ) : min a b = a ∨ min a b = b := by
    rcases le_total a b with h | h
    · exact Or.inl (min_eq_left h)
    · exact Or.inr (min_eq_right h)
  rcases hmin (min (z 0 : ℝ) (1 - z 0)) (min (z 1 : ℝ) (1 - z 1)) with h | h
  · exact ⟨0, (hmin (z 0 : ℝ) (1 - z 0)).imp (h.trans ·) (h.trans ·)⟩
  · exact ⟨1, (hmin (z 1 : ℝ) (1 - z 1)).imp (h.trans ·) (h.trans ·)⟩

private theorem squareDepth_continuous : Continuous squareDepth := by
  unfold squareDepth
  fun_prop

private theorem squareCollarDenom_pos (s : I) : 0 < 1 - (s : ℝ) / 2 := by
  have hs := s.2.2
  linarith

/-- The inner square expands to the whole square; points in the collar hit its boundary. -/
private def squareCollarExpand (s : I) (z : Square) : Square := fun i =>
  Set.projIcc 0 1 zero_le_one (((z i : ℝ) - (s : ℝ) / 4) / (1 - (s : ℝ) / 2))

private theorem squareCollarExpand_continuous :
    Continuous (fun sz : I × Square => squareCollarExpand sz.1 sz.2) := by
  apply continuous_pi
  intro i
  apply continuous_projIcc.comp
  exact ((((continuous_apply i).comp continuous_snd).subtype_val.sub
    (continuous_fst.subtype_val.div_const 4)).div
    (continuous_const.sub (continuous_fst.subtype_val.div_const 2))
    (fun sz => ne_of_gt (squareCollarDenom_pos sz.1)))

private theorem squareCollarExpand_zero (z : Square) : squareCollarExpand 0 z = z := by
  funext i
  simpa only [squareCollarExpand, Set.Icc.coe_zero, zero_div, sub_zero,
    div_one] using Set.projIcc_val zero_le_one (z i)

private theorem squareCollarExpand_boundary (s : I) (z : Square)
    (hz : squareDepth z ≤ (s : ℝ) / 4) :
    squareCollarExpand s z ∈ Cube.boundary (Fin 2) := by
  obtain ⟨i, hi | hi⟩ := squareDepth_coordinate z
  · refine ⟨i, Or.inl ?_⟩
    apply projIcc_eq_zero.mpr
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · exact (squareCollarDenom_pos s).le
  · refine ⟨i, Or.inr ?_⟩
    apply projIcc_eq_one.mpr
    apply (le_div_iff₀ (squareCollarDenom_pos s)).mpr
    linarith

/-- Time stops at the collar, whose boundary is always at time zero. -/
private def squareCollarTime (s : I) (z : Square) : I :=
  ⟨min (s : ℝ) (4 * squareDepth z),
    le_min s.2.1 (mul_nonneg (by norm_num) (squareDepth_nonneg z)),
    (min_le_left _ _).trans s.2.2⟩

private theorem squareCollarTime_continuous :
    Continuous (fun sz : I × Square => squareCollarTime sz.1 sz.2) :=
  (continuous_fst.subtype_val.min
    (continuous_const.mul (squareDepth_continuous.comp continuous_snd))).subtype_mk _

private theorem squareCollarTime_zero (z : Square) : squareCollarTime 0 z = 0 := by
  apply Subtype.ext
  exact min_eq_left (mul_nonneg (by norm_num) (squareDepth_nonneg z))

private theorem squareCollarTime_boundary (s : I) (z : Square)
    (hz : z ∈ Cube.boundary (Fin 2)) : squareCollarTime s z = 0 := by
  apply Subtype.ext
  simp only [squareCollarTime, squareDepth_boundary z hz, mul_zero]
  exact min_eq_right s.2.1

/-- Constant boundary values are allowed to depend on homotopy time. -/
def SquareConstantBoundary {X : Type*} [TopologicalSpace X] (f : C((Fin 2 → I), X)) : Prop :=
  ∀ z ∈ Cube.boundary (Fin 2), f z = f (fun _ => 0)

/-- A null homotopy with moving but constant boundary gives a based null homotopy.
The first stage inserts a collar. The second contracts the resulting radial path. -/
theorem genLoop_null_of_movingBoundary {X : Type*} [TopologicalSpace X] {x y : X}
    (p : GenLoop (Fin 2) X x)
    (H : ContinuousMap.HomotopyWith p.val (ContinuousMap.const _ y) SquareConstantBoundary) :
    GenLoop.Homotopic p GenLoop.const := by
  let z₀ : Fin 2 → I := squareOrigin
  have hz₀ : z₀ ∈ Cube.boundary (Fin 2) := squareOrigin_boundary
  let h : C(I, X) := H.toContinuousMap.comp
    ⟨fun t => (t, z₀), continuous_id.prodMk continuous_const⟩
  have hzero : h 0 = x := (H.apply_zero z₀).trans (GenLoop.boundary p z₀ hz₀)
  let r : C((Fin 2 → I), I) :=
    ⟨squareCollarTime 1, squareCollarTime_continuous.comp
      (continuous_const.prodMk continuous_id)⟩
  let q : GenLoop (Fin 2) X x := ⟨h.comp r, fun z hz => by
    change h (squareCollarTime 1 z) = x
    rw [squareCollarTime_boundary 1 z hz]
    exact hzero⟩
  have hfirst : GenLoop.Homotopic p q := by
    refine ⟨{
      toFun := fun sz => H (squareCollarTime sz.1 sz.2,
        squareCollarExpand sz.1 sz.2)
      continuous_toFun := H.continuous.comp
        (squareCollarTime_continuous.prodMk squareCollarExpand_continuous)
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro z
      rw [squareCollarTime_zero, squareCollarExpand_zero]
      exact H.apply_zero z
    · intro z
      change H (squareCollarTime 1 z, squareCollarExpand 1 z) =
        H (squareCollarTime 1 z, z₀)
      by_cases hd : 1 ≤ 4 * squareDepth z
      · have ht : squareCollarTime 1 z = 1 := Subtype.ext (min_eq_left hd)
        rw [ht, H.apply_one, H.apply_one]
        rfl
      · apply H.prop
        apply squareCollarExpand_boundary
        have hlt := lt_of_not_ge hd
        change squareDepth z ≤ (1 : ℝ) / 4
        linarith
    · intro s z hz
      change H (squareCollarTime s z, squareCollarExpand s z) = p z
      rw [squareCollarTime_boundary s z hz, H.apply_zero, GenLoop.boundary p z hz]
      exact GenLoop.boundary p _ (squareCollarExpand_boundary s z (by
        rw [squareDepth_boundary z hz]
        exact div_nonneg s.2.1 (by norm_num)))
  have hsecond : GenLoop.Homotopic q GenLoop.const := by
    refine ⟨{
      toFun := fun sz => h (unitInterval.symm sz.1 * r sz.2)
      continuous_toFun := h.continuous.comp (by
        apply Continuous.subtype_mk
        exact (continuous_subtype_val.comp
          (unitInterval.continuous_symm.comp continuous_fst)).mul
            (continuous_subtype_val.comp (r.continuous.comp continuous_snd)))
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro z
      change h (unitInterval.symm 0 * r z) = h (r z)
      simp
    · intro z
      change h (unitInterval.symm 1 * r z) = x
      simpa using hzero
    · intro s z hz
      change h (unitInterval.symm s * squareCollarTime 1 z) = h (squareCollarTime 1 z)
      rw [squareCollarTime_boundary 1 z hz, mul_zero]
  exact hfirst.trans hsecond

end Whitehead
