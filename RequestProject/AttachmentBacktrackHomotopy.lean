module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.AttachmentBaseChange
public import RequestProject.CylinderBoundaryHomotopyCorrection

@[expose] public section

/-! Cancelling a homotopy of attaching maps followed by its reverse. The
boundary contraction is explicit; full-cylinder extension makes the disk
homotopy stationary on the attaching boundary. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

def backtrackTime (t : I) : I :=
  ⟨min (2 * (t : ℝ)) (2 - 2 * (t : ℝ)), by
    have hl := t.2.1
    have hu := t.2.2
    constructor
    · apply le_min <;> linarith
    · rcases le_total (t : ℝ) (1 / 2) with h | h
      · exact (min_le_left _ _).trans (by linarith)
      · exact (min_le_right _ _).trans (by linarith)⟩

theorem backtrackTime_continuous : Continuous backtrackTime := by
  unfold backtrackTime
  fun_prop

theorem backtrackTime_zero : backtrackTime 0 = 0 := by
  apply Subtype.ext
  norm_num [backtrackTime]

theorem backtrackTime_one : backtrackTime 1 = 0 := by
  apply Subtype.ext
  norm_num [backtrackTime]

universe u
variable {D P : Type u} [TopologicalSpace D] [TopologicalSpace P]

/-- The composite of the two actual collar maps is homotopic to the
identity. All map equations below are discharged by `desc` in the final
construction of the attaching-homotopy equivalence. -/
theorem attachingBacktrack_homotopic_id (S : Set D) (hS : IsClosed S)
    (hfull : HasHomotopyExtension (Subtype.val : FullCylinderBoundary S → I × D))
    (a₀ a₁ : C(S, P)) (H : a₀.Homotopy a₁)
    (C : C(Space a₁ Subtype.val, Space a₀ Subtype.val))
    (B : C(Space a₀ Subtype.val, Space a₁ Subtype.val))
    (hCold : ∀ p, C (old a₁ Subtype.val p) = old a₀ Subtype.val p)
    (hBold : ∀ p, B (old a₀ Subtype.val p) = old a₁ Subtype.val p)
    (L₀ : C(I × D, Space a₀ Subtype.val))
    (L₁ : C(I × D, Space a₁ Subtype.val))
    (hL₀zero : ∀ d, L₀ (0, d) = cell a₀ Subtype.val d)
    (hL₁zero : ∀ d, L₁ (0, d) = cell a₁ Subtype.val d)
    (hL₀side : ∀ t a, L₀ (t, a.val) = old a₀ Subtype.val (H (t, a)))
    (hL₁side : ∀ t a, L₁ (t, a.val) = old a₁ Subtype.val (H.symm (t, a)))
    (hCcell : ∀ d, C (cell a₁ Subtype.val d) = L₀ (1, d))
    (hBcell : ∀ d, B (cell a₀ Subtype.val d) = L₁ (1, d)) :
    (C.comp B).Homotopic (ContinuousMap.id (Space a₀ Subtype.val)) := by
  let f₀ : C(D, Space a₀ Subtype.val) := ⟨cell a₀ Subtype.val, cell_continuous _ _⟩
  let fm : C(D, Space a₀ Subtype.val) :=
    C.comp ⟨cell a₁ Subtype.val, cell_continuous _ _⟩
  let f₁ : C(D, Space a₀ Subtype.val) := (C.comp B).comp f₀
  let F₀ : f₀.Homotopy fm := {
    toContinuousMap := L₀
    map_zero_left := hL₀zero
    map_one_left := fun d => (hCcell d).symm }
  let F₁ : fm.Homotopy f₁ := {
    toContinuousMap := C.comp L₁
    map_zero_left := fun d => congrArg C (hL₁zero d)
    map_one_left := fun d => congrArg C (hBcell d).symm }
  let F : f₀.Homotopy f₁ := F₀.trans F₁
  have hFside (t : I) (a : S) :
      F (t, a.val) = old a₀ Subtype.val (H (backtrackTime t, a)) := by
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · change L₀ (_, a.val) = _
      rw [hL₀side]
      congr 2
      refine Prod.ext ?_ rfl
      apply Subtype.ext
      change 2 * (t : ℝ) = min (2 * (t : ℝ)) (2 - 2 * (t : ℝ))
      exact (min_eq_left (by linarith)).symm
    · change C (L₁ (_, a.val)) = _
      rw [hL₁side, hCold]
      change old a₀ Subtype.val (H (unitInterval.symm _, a)) = _
      congr 2
      refine Prod.ext ?_ rfl
      apply Subtype.ext
      change 1 - (2 * (t : ℝ) - 1) = min (2 * (t : ℝ)) (2 - 2 * (t : ℝ))
      rw [min_eq_right (by linarith)]
      ring
  have htime : Continuous (fun sta : I × (I × S) =>
      unitInterval.symm sta.1 * backtrackTime sta.2.1) := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp
      (unitInterval.continuous_symm.comp continuous_fst)).mul
        (continuous_subtype_val.comp
          (backtrackTime_continuous.comp (continuous_fst.comp continuous_snd)))
  let J : C(I × (I × S), Space a₀ Subtype.val) := {
    toFun := fun sta => old a₀ Subtype.val
      (H (unitInterval.symm sta.1 * backtrackTime sta.2.1, sta.2.2))
    continuous_toFun := (old_continuous _ _).comp (H.continuous.comp
      (htime.prodMk (continuous_snd.comp continuous_snd))) }
  have hJ₀ (t : I) (a : S) : J (0, (t, a)) = F (t, a.val) := by
    change old a₀ Subtype.val (H (unitInterval.symm 0 * backtrackTime t, a)) = _
    simpa using (hFside t a).symm
  have hJ₁ (t : I) (a : S) : J (1, (t, a)) = f₀ a.val := by
    change old a₀ Subtype.val (H (unitInterval.symm 1 * backtrackTime t, a)) =
      cell a₀ Subtype.val a.val
    simp only [unitInterval.symm_one, zero_mul, H.apply_zero]
    exact (cell_boundary a₀ Subtype.val Subtype.val_injective a).symm
  have hJl (s : I) (a : S) : J (s, (0, a)) = f₀ a.val := by
    change old a₀ Subtype.val (H (unitInterval.symm s * backtrackTime 0, a)) =
      cell a₀ Subtype.val a.val
    rw [backtrackTime_zero, mul_zero, H.apply_zero]
    exact (cell_boundary a₀ Subtype.val Subtype.val_injective a).symm
  have hJr (s : I) (a : S) : J (s, (1, a)) = f₁ a.val := by
    change old a₀ Subtype.val (H (unitInterval.symm s * backtrackTime 1, a)) =
      C (B (cell a₀ Subtype.val a.val))
    rw [backtrackTime_one, mul_zero, H.apply_zero,
      cell_boundary a₀ Subtype.val Subtype.val_injective, hBold, hCold]
  obtain ⟨G⟩ := homotopyRel_of_boundaryContraction S hS hfull F J hJ₀ hJ₁ hJl hJr
  let HOld : C(I × P, Space a₀ Subtype.val) :=
    ⟨fun tp => old a₀ Subtype.val tp.2, (old_continuous _ _).comp continuous_snd⟩
  have hg : ∀ t a, HOld (t, a₀ a) = G (t, a.val) := by
    intro t a
    change old a₀ Subtype.val (a₀ a) = G (t, a.val)
    rw [G.eq_fst t a.property]
    exact (cell_boundary a₀ Subtype.val Subtype.val_injective a).symm
  let T := attachmentHomotopyPasting a₀ Subtype.val HOld G.toContinuousMap hg
  have Htotal : ContinuousMap.Homotopy (ContinuousMap.id (Space a₀ Subtype.val))
      (C.comp B) := {
    toContinuousMap := T
    map_zero_left := by
      intro z
      obtain ⟨w, rfl⟩ := quotientMap_surjective a₀ Subtype.val z
      cases w with
      | inl p => rfl
      | inr d => exact (attachmentHomotopyPasting_cell a₀ Subtype.val
          HOld G.toContinuousMap hg 0 d).trans (G.apply_zero d)
    map_one_left := by
      intro z
      obtain ⟨w, rfl⟩ := quotientMap_surjective a₀ Subtype.val z
      cases w with
      | inl p => exact ((congrArg C (hBold p)).trans (hCold p)).symm
      | inr d => exact (attachmentHomotopyPasting_cell a₀ Subtype.val
          HOld G.toContinuousMap hg 1 d).trans (G.apply_one d) }
  exact ⟨Htotal.symm⟩

end FiniteChains.RelativeAttachment
