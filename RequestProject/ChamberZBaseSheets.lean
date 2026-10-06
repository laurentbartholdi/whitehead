import RequestProject.ChamberZBaseGeneration

/-! Extraction of actual base-copy cycles from the modified-chamber base. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
open scoped Classical
universe u
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {M : CayGroup A → Prop} {att : NeSpx A →o X}

def zBaseMark (z : ZBase (A := A) (X := X) (M := M) (att := att)) :
    {w : CayGroup A // M w} :=
  match z with
  | ⟨Sum.inl _, h⟩ => False.elim h
  | ⟨Sum.inr wx, _⟩ => wx.1

def zBaseRead (z : ZBase (A := A) (X := X) (M := M) (att := att)) : X :=
  match z with
  | ⟨Sum.inl _, h⟩ => False.elim h
  | ⟨Sum.inr wx, _⟩ => wx.2

theorem zBase_le_iff (a b : ZBase (A := A) (X := X) (M := M) (att := att)) :
    a ≤ b ↔ zBaseMark a = zBaseMark b ∧ zBaseRead a ≤ zBaseRead b := by
  rcases a with ⟨a | ax, ha⟩
  · exact ha.elim
  · rcases b with ⟨b | bx, hb⟩
    · exact hb.elim
    · rfl

theorem zBaseRead_strictMono :
    StrictMono (zBaseRead (A := A) (X := X) (M := M) (att := att)) := by
  intro a b hab
  have h := (zBase_le_iff a b).mp hab.le
  refine lt_of_le_not_ge h.2 ?_
  intro hba
  exact hab.not_ge ((zBase_le_iff b a).mpr ⟨h.1.symm, hba⟩)

def zBaseReadCx : Hom (strictOrderCx (ZBase (A := A) (X := X) (M := M) (att := att)))
    (strictOrderCx X) := strictOrderCxMap zBaseRead zBaseRead_strictMono

def zBaseCopy (w : {w : CayGroup A // M w}) (x : X) :
    ZBase (A := A) (X := X) (M := M) (att := att) := ⟨Sum.inr (w, x), trivial⟩

theorem zBaseCopy_strictMono (w : {w : CayGroup A // M w}) :
    StrictMono (zBaseCopy (A := A) (X := X) (M := M) (att := att) w) := by
  intro a b hab
  refine lt_of_le_not_ge ((zBase_le_iff _ _).mpr ⟨rfl, hab.le⟩) ?_
  intro hba
  exact hab.not_ge ((zBase_le_iff _ _).mp hba).2

def zBaseCopyCx (w : {w : CayGroup A // M w}) :
    Hom (strictOrderCx X)
      (strictOrderCx (ZBase (A := A) (X := X) (M := M) (att := att))) :=
  strictOrderCxMap (zBaseCopy w) (zBaseCopy_strictMono w)

theorem zBaseCopy_read (w : {w : CayGroup A // M w})
    (z : ZBase (A := A) (X := X) (M := M) (att := att))
    (hz : zBaseMark z = w) : zBaseCopy w (zBaseRead z) = z := by
  rcases z with ⟨z | wx, h⟩
  · exact h.elim
  · apply Subtype.ext
    change Sum.inr (w, wx.2) = Sum.inr wx
    exact congrArg Sum.inr (Prod.ext hz.symm rfl)

theorem zBase_triangle_marks (t : StrictOrdTri
    (ZBase (A := A) (X := X) (M := M) (att := att))) :
    zBaseMark t.1.1 = zBaseMark t.1.2.1 ∧
      zBaseMark t.1.1 = zBaseMark t.1.2.2 := by
  exact ⟨((zBase_le_iff _ _).mp t.2.1.le).1,
    ((zBase_le_iff _ _).mp (t.2.1.trans t.2.2).le).1⟩

/-- Filtering to one actual inserted copy commutes with the cellular boundary. -/
theorem zBase_sheet_boundary (w : {w : CayGroup A // M w})
    (c : StrictOrdTri (ZBase (A := A) (X := X) (M := M) (att := att)) →₀ ℤ) :
    Comb.bdry2 (strictOrderCx (ZBase (A := A) (X := X) (M := M) (att := att)))
      (c.filter (fun t => zBaseMark t.1.1 = w)) =
    (Comb.bdry2 (strictOrderCx (ZBase (A := A) (X := X) (M := M) (att := att))) c).filter
      (fun e => zBaseMark e.1.1 = w) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [Finsupp.filter_zero, map_zero]
  | add c d hc hd => rw [Finsupp.filter_add, map_add, hc, hd, map_add, Finsupp.filter_add]
  | single t n =>
    obtain ⟨hab, hac⟩ := zBase_triangle_marks t
    by_cases hw : zBaseMark t.1.1 = w
    · have hbw : zBaseMark t.1.2.1 = w := hab.symm.trans hw
      simp [Finsupp.filter_single_of_pos, hw, hbw, Comb.bdry2, strictOrderCx,
        pathChain, Finsupp.filter_add, LinearMap.map_zero]
    · have hbw : zBaseMark t.1.2.1 ≠ w := fun h => hw (hab.trans h)
      simp [Finsupp.filter_single_of_neg, hw, hbw, Comb.bdry2, strictOrderCx,
        pathChain, Finsupp.filter_add, LinearMap.map_zero]

/-- The restriction of an actual base cycle to one inserted copy is a cycle of the
original base after reading its vertices back in that copy. -/
theorem zBase_sheet_read_cycle (w : {w : CayGroup A // M w})
    (c : StrictOrdTri (ZBase (A := A) (X := X) (M := M) (att := att)) →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx
      (ZBase (A := A) (X := X) (M := M) (att := att))) c = 0) :
    Comb.bdry2 (strictOrderCx X)
      (chain2 (zBaseReadCx (A := A) (X := X) (M := M) (att := att))
        (c.filter (fun t => zBaseMark t.1.1 = w))) = 0 := by
  rw [bdry2_chain2, zBase_sheet_boundary, hc, Finsupp.filter_zero, map_zero]

/-- Reading one sheet and inserting it back retains every coefficient of that sheet. -/
theorem zBase_sheet_reinsert (w : {w : CayGroup A // M w})
    (c : StrictOrdTri (ZBase (A := A) (X := X) (M := M) (att := att)) →₀ ℤ) :
    chain2 (zBaseCopyCx w) (chain2 zBaseReadCx
      (c.filter (fun t => zBaseMark t.1.1 = w))) =
      c.filter (fun t => zBaseMark t.1.1 = w) := by
  change Finsupp.mapDomain (zBaseCopyCx w).onF
    (Finsupp.mapDomain zBaseReadCx.onF (c.filter (fun t => zBaseMark t.1.1 = w))) = _
  induction c using Finsupp.induction_linear with
  | zero => simp only [Finsupp.filter_zero, Finsupp.mapDomain_zero]
  | add c d hc hd =>
      rw [Finsupp.filter_add, Finsupp.mapDomain_add, Finsupp.mapDomain_add, hc, hd,
        Finsupp.filter_add]
  | single t n =>
      by_cases hw : zBaseMark t.1.1 = w
      · obtain ⟨hab, hac⟩ := zBase_triangle_marks t
        have he : (zBaseCopyCx w).onF (zBaseReadCx.onF t) = t := by
          apply Subtype.ext
          exact Prod.ext (zBaseCopy_read w _ hw)
            (Prod.ext (zBaseCopy_read w _ (hab.symm.trans hw))
              (zBaseCopy_read w _ (hac.symm.trans hw)))
        simp only [Finsupp.filter_single_of_pos, hw, Finsupp.mapDomain_single, he]
      · simp [Finsupp.filter_single_of_neg, hw]

/-- Only finitely many inserted copies meet the support, and their restrictions recover
the original chain exactly. -/
theorem zBase_chain_sum_sheets
    (c : StrictOrdTri (ZBase (A := A) (X := X) (M := M) (att := att)) →₀ ℤ) :
    ∑ w ∈ c.support.image (fun t => zBaseMark t.1.1),
      c.filter (fun t => zBaseMark t.1.1 = w) = c := by
  ext t
  by_cases ht : c t = 0
  · simp [Finsupp.filter_apply, ht]
  · have hm : zBaseMark t.1.1 ∈ c.support.image (fun t => zBaseMark t.1.1) :=
      Finset.mem_image.mpr ⟨t, Finsupp.mem_support_iff.mpr ht, rfl⟩
    simp only [Finsupp.finset_sum_apply, Finsupp.filter_apply]
    rw [Finset.sum_eq_single (zBaseMark t.1.1)]
    · simp
    · intro w _ hw
      simp [Ne.symm hw]
    · exact fun h => False.elim (h hm)

/-- Every actual base-subcomplex two-cycle is a finite sum of images of cycles of
the original base, one from each inserted copy meeting its support. -/
theorem exists_zBase_cycle_decomposition
    (c : StrictOrdTri (ZBase (A := A) (X := X) (M := M) (att := att)) →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx
      (ZBase (A := A) (X := X) (M := M) (att := att))) c = 0) :
    ∃ (s : Finset {w : CayGroup A // M w})
      (d : {w : CayGroup A // M w} → (StrictOrdTri X →₀ ℤ)),
      (∀ w, Comb.bdry2 (strictOrderCx X) (d w) = 0) ∧
        c = ∑ w ∈ s, chain2 (zBaseCopyCx w) (d w) := by
  refine ⟨c.support.image (fun t => zBaseMark t.1.1),
    fun w => chain2 zBaseReadCx (c.filter (fun t => zBaseMark t.1.1 = w)),
    fun w => zBase_sheet_read_cycle w c hc, ?_⟩
  symm
  calc
    _ = ∑ w ∈ c.support.image (fun t => zBaseMark t.1.1),
        c.filter (fun t => zBaseMark t.1.1 = w) := by
      apply Finset.sum_congr rfl
      intro w _
      exact zBase_sheet_reinsert w c
    _ = c := zBase_chain_sum_sheets c

end FiniteChains.Davis
