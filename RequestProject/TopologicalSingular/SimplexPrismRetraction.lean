module

public import RequestProject.TopologicalSingular.SingularChains

@[expose] public section

/-! An explicit retraction of a simplex prism onto its bottom and its sides.
The radial projection is taken from height two above the barycentre. Its
denominator is bounded below by one half, including at the barycentre. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology

noncomputable def simplexMin {n : ℕ} (z : Domain n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty z.val

theorem simplexMin_nonneg {n : ℕ} (z : Domain n) : 0 ≤ simplexMin z :=
  Finset.le_inf' _ _ (fun i _ => z.property.1 i)

theorem simplexMin_le {n : ℕ} (z : Domain n) (i : Fin (n + 1)) : simplexMin z ≤ z.val i :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem simplexMin_attained {n : ℕ} (z : Domain n) : ∃ i, simplexMin z = z.val i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty z.val
  exact ⟨i, hi⟩

theorem simplexMin_continuous (n : ℕ) : Continuous (simplexMin (n := n)) := by
  exact Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun i _ => (continuous_apply i).comp continuous_subtype_val)

def simplexBoundary (n : ℕ) : Set (Domain n) := {z | ∃ i, z.val i = 0}

theorem simplexMin_eq_zero_iff {n : ℕ} (z : Domain n) :
    simplexMin z = 0 ↔ z ∈ simplexBoundary n := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := simplexMin_attained z
    exact ⟨i, hi.symm.trans h⟩
  · rintro ⟨i, hi⟩
    exact le_antisymm (hi ▸ simplexMin_le z i) (simplexMin_nonneg z)

theorem simplexBoundary_isClosed (n : ℕ) : IsClosed (simplexBoundary n) := by
  have he : simplexBoundary n = {z | simplexMin z = 0} := by
    ext z
    exact (simplexMin_eq_zero_iff z).symm
  rw [he]
  exact isClosed_eq (simplexMin_continuous n) continuous_const

noncomputable def prismDenom {n : ℕ} (w : I × Domain n) : ℝ :=
  max (1 - (w.1 : ℝ) / 2) (1 - (n + 1 : ℝ) * simplexMin w.2)

theorem prismDenom_pos {n : ℕ} (w : I × Domain n) : 0 < prismDenom w := by
  have h := le_max_left (1 - (w.1 : ℝ) / 2) (1 - (n + 1 : ℝ) * simplexMin w.2)
  have ht := w.1.property.2
  change 1 - (w.1 : ℝ) / 2 ≤ prismDenom w at h
  linarith

theorem prismDenom_le_one {n : ℕ} (w : I × Domain n) : prismDenom w ≤ 1 := by
  apply max_le
  · linarith [w.1.property.1]
  · have hp : 0 ≤ (n + 1 : ℝ) * simplexMin w.2 := mul_nonneg (by positivity) (simplexMin_nonneg _)
    linarith

theorem prismDenom_continuous (n : ℕ) : Continuous (prismDenom (n := n)) := by
  exact (continuous_const.sub (continuous_fst.subtype_val.div_const 2)).max
    (continuous_const.sub (continuous_const.mul ((simplexMin_continuous n).comp continuous_snd)))

theorem prismDenom_eq_one {n : ℕ} (w : I × Domain n)
    (h : w.1 = 0 ∨ w.2 ∈ simplexBoundary n) : prismDenom w = 1 := by
  apply le_antisymm (prismDenom_le_one w)
  rcases h with h | h
  · have he : 1 - (w.1 : ℝ) / 2 = 1 := by rw [h]; norm_num
    exact he ▸ le_max_left _ _
  · have hm := (simplexMin_eq_zero_iff w.2).mpr h
    have he : 1 - (n + 1 : ℝ) * simplexMin w.2 = 1 := by rw [hm]; ring
    exact he ▸ le_max_right _ _

noncomputable def prismRetractTime {n : ℕ} (w : I × Domain n) : I :=
  ⟨2 + ((w.1 : ℝ) - 2) / prismDenom w, by
    have hd := prismDenom_pos w
    have htime : 1 - (w.1 : ℝ) / 2 ≤ prismDenom w := le_max_left _ _
    have hu := prismDenom_le_one w
    constructor
    · have he : (-2) ≤ ((w.1 : ℝ) - 2) / prismDenom w :=
        (le_div_iff₀ hd).mpr (by linarith)
      linarith
    · have he : ((w.1 : ℝ) - 2) / prismDenom w ≤ -1 :=
        (div_le_iff₀ hd).mpr (by linarith [w.1.property.2])
      linarith⟩

noncomputable def prismRetractPoint {n : ℕ} (w : I × Domain n) : Domain n :=
  ⟨fun i => (w.2.val i - (1 - prismDenom w) / (n + 1 : ℝ)) / prismDenom w, by
    have hd := prismDenom_pos w
    have hk : 0 < (n + 1 : ℝ) := by positivity
    constructor
    · intro i
      apply div_nonneg _ hd.le
      apply sub_nonneg.mpr
      apply (div_le_iff₀ hk).mpr
      have hspace : 1 - (n + 1 : ℝ) * simplexMin w.2 ≤ prismDenom w := le_max_right _ _
      have hm := simplexMin_le w.2 i
      nlinarith
    · rw [← Finset.sum_div, Finset.sum_sub_distrib, w.2.property.2]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one]
      field_simp [ne_of_gt hd, ne_of_gt hk]
      ring⟩

theorem prismRetractTime_continuous (n : ℕ) : Continuous (prismRetractTime (n := n)) := by
  apply Continuous.subtype_mk
  exact continuous_const.add ((continuous_fst.subtype_val.sub continuous_const).div
    (prismDenom_continuous n) (fun w => ne_of_gt (prismDenom_pos w)))

theorem prismRetractPoint_continuous (n : ℕ) : Continuous (prismRetractPoint (n := n)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (((continuous_apply i).comp continuous_snd.subtype_val).sub
    ((continuous_const.sub (prismDenom_continuous n)).div_const _)).div
      (prismDenom_continuous n) (fun w => ne_of_gt (prismDenom_pos w))

def simplexPrismSide (n : ℕ) : Set (I × Domain n) :=
  {w | w.1 = 0 ∨ w.2 ∈ simplexBoundary n}

theorem prismRetract_mem {n : ℕ} (w : I × Domain n) :
    (prismRetractTime w, prismRetractPoint w) ∈ simplexPrismSide n := by
  have hd := prismDenom_pos w
  have hk : (n + 1 : ℝ) ≠ 0 := by positivity
  rcases le_total (1 - (w.1 : ℝ) / 2) (1 - (n + 1 : ℝ) * simplexMin w.2) with h | h
  · right
    obtain ⟨i, hi⟩ := simplexMin_attained w.2
    refine ⟨i, ?_⟩
    change (w.2.val i - (1 - prismDenom w) / (n + 1 : ℝ)) / prismDenom w = 0
    rw [prismDenom, max_eq_right h, ← hi]
    field_simp [hk]
    ring
  · left
    apply Subtype.ext
    change 2 + ((w.1 : ℝ) - 2) / prismDenom w = 0
    have he : prismDenom w = 1 - (w.1 : ℝ) / 2 := max_eq_left h
    have hq : ((w.1 : ℝ) - 2) / prismDenom w = -2 := by
      apply (div_eq_iff (ne_of_gt hd)).mpr
      rw [he]
      ring
    rw [hq]
    ring

/-- Radial retraction onto the bottom and all boundary faces of a prism. -/
noncomputable def simplexPrismRetraction (n : ℕ) : C(I × Domain n, simplexPrismSide n) where
  toFun w := ⟨(prismRetractTime w, prismRetractPoint w), prismRetract_mem w⟩
  continuous_toFun := (prismRetractTime_continuous n).prodMk
    (prismRetractPoint_continuous n) |>.subtype_mk _

theorem simplexPrismRetraction_fixes {n : ℕ} (w : I × Domain n) (hw : w ∈ simplexPrismSide n) :
    (simplexPrismRetraction n w).val = w := by
  have hd := prismDenom_eq_one w hw
  apply Prod.ext
  · apply Subtype.ext
    change 2 + ((w.1 : ℝ) - 2) / prismDenom w = (w.1 : ℝ)
    rw [hd]
    ring
  · apply Subtype.ext
    funext i
    change (w.2.val i - (1 - prismDenom w) / (n + 1 : ℝ)) / prismDenom w = w.2.val i
    rw [hd]
    simp

end FiniteChains.TopologicalSingular
