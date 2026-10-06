module

public import RequestProject.GenusBoundaryCoordinates

@[expose] public section

/-! Distinguished first-edge detection for the actual geometric marking loops. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Cell
variable (q : ℕ) [NeZero q]

abbrev MarkingSurfaceCell := SCell (gvc q) (gec q) (gc q)
abbrev MarkingSurfaceEdge := (orderCx (NeSpx (cmpRel (MarkingSurfaceCell q)))).E

def markingBaseCell : MarkingSurfaceCell q := .vtx none
def markingMidCell (i : Fin q × Bool) : MarkingSurfaceCell q := .vtx (some i)
def markingBedCell (i : Fin q × Bool) (b : Bool) : MarkingSurfaceCell q :=
  .bed (i.1, i.2, b)

theorem markingBaseLe (i : Fin q × Bool) (b : Bool) :
    markingBaseCell q ≤ markingBedCell q i b := by
  cases b with
  | false =>
    simpa only [cV, cE, gvc_markedBoundaryPos_false, gec_markedBoundaryPos,
      markingBaseCell, markingBedCell, toS] using
      cV_le_cE (gc q) (markedBoundaryPos q i false)
  | true =>
    simpa only [cV, cE, gvc_markedBoundaryPos_end, gec_markedBoundaryPos,
      markingBaseCell, markingBedCell, toS] using
      cV1_le_cE (gc q) (markedBoundaryPos q i true)

theorem markingMidLe (i : Fin q × Bool) (b : Bool) :
    markingMidCell q i ≤ markingBedCell q i b := by
  cases b with
  | false =>
    simpa only [markedBoundaryPos_succ, cV, cE, gvc_markedBoundaryPos_true,
      gec_markedBoundaryPos, markingMidCell, markingBedCell, toS] using
      cV1_le_cE (gc q) (markedBoundaryPos q i false)
  | true =>
    simpa only [cV, cE, gvc_markedBoundaryPos_true, gec_markedBoundaryPos,
      markingMidCell, markingBedCell, toS] using
      cV_le_cE (gc q) (markedBoundaryPos q i true)

def markingBaseFlag (i : Fin q × Bool) (b : Bool) : MarkingSurfaceEdge q :=
  ⟨(spx1 (markingBaseCell q), spx2 (markingBaseLe q i b)),
    spx1_le_spx2_left (markingBaseLe q i b)⟩

def markingBedBaseFlag (i : Fin q × Bool) (b : Bool) : MarkingSurfaceEdge q :=
  ⟨(spx1 (markingBedCell q i b), spx2 (markingBaseLe q i b)),
    spx1_le_spx2_right (markingBaseLe q i b)⟩

def markingMidFlag (i : Fin q × Bool) (b : Bool) : MarkingSurfaceEdge q :=
  ⟨(spx1 (markingMidCell q i), spx2 (markingMidLe q i b)),
    spx1_le_spx2_left (markingMidLe q i b)⟩

def markingBedMidFlag (i : Fin q × Bool) (b : Bool) : MarkingSurfaceEdge q :=
  ⟨(spx1 (markingBedCell q i b), spx2 (markingMidLe q i b)),
    spx1_le_spx2_right (markingMidLe q i b)⟩

/-- The edge detecting the marking `i`, traversed positively at its start. -/
def markingFirstEdge (i : Fin q × Bool) : MarkingSurfaceEdge q := markingBaseFlag q i false

def markingTail (i : Fin q × Bool) : List (MarkingSurfaceEdge q × Bool) :=
  [(markingBedBaseFlag q i false, false),
    (markingBedMidFlag q i false, true),
    (markingMidFlag q i false, false),
    (markingMidFlag q i true, true),
    (markingBedMidFlag q i true, false),
    (markingBedBaseFlag q i true, true),
    (markingBaseFlag q i true, false)]

/-- This is an equality of the original geometric paths, before passing to
path chains or projecting any cover sheets. -/
theorem gSig_first_edge (i : Fin q × Bool) :
    gSig q (i.1.val, i.2) = (markingFirstEdge q i, true) :: markingTail q i := by
  rw [gSig_boundary_path]
  simp only [bdEdge, edgeHop, edgeHopRev, hop, List.cons_append, List.nil_append,
    ordPos, ordNeg, markedBoundaryPos_succ, cV, cE,
    gvc_markedBoundaryPos_false, gvc_markedBoundaryPos_true,
    gvc_markedBoundaryPos_end, gec_markedBoundaryPos]
  rfl

theorem markingFirstEdge_source (i : Fin q × Bool) :
    (orderCx (NeSpx (cmpRel (MarkingSurfaceCell q)))).src (markingFirstEdge q i) = gBase q := by
  change spx1 (markingBaseCell q) = spx1 (cV (gc q) (cyc (8 * q) 0))
  rw [cV, gvc_even q (by decide : 0 % 2 = 0)]
  rfl

theorem markingBaseFlag_eq_iff (i j : Fin q × Bool) (b c : Bool) :
    markingBaseFlag q i b = markingBaseFlag q j c ↔ i = j ∧ b = c := by
  constructor
  · intro h
    have ht := congrArg (fun e : MarkingSurfaceEdge q => e.1.2.1) h
    change ({markingBaseCell q, markingBedCell q i b} : Finset (MarkingSurfaceCell q)) =
      {markingBaseCell q, markingBedCell q j c} at ht
    have hm : markingBedCell q i b ∈
        ({markingBaseCell q, markingBedCell q j c} : Finset (MarkingSurfaceCell q)) := by
      rw [← ht]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · cases hm
    · have he : (i.1, i.2, b) = (j.1, j.2, c) := Cell.bed.inj hm
      exact ⟨congrArg (fun x : Fin q × Bool × Bool => (x.1, x.2.1)) he,
        congrArg (fun x : Fin q × Bool × Bool => x.2.2) he⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem markingFirstEdge_injective : Function.Injective (markingFirstEdge q) := by
  intro i j h
  exact ((markingBaseFlag_eq_iff q i j false false).mp h).1

theorem markingFirstEdge_ne_base_true (i j : Fin q × Bool) :
    markingFirstEdge q i ≠ markingBaseFlag q j true := by
  intro h
  have hf := ((markingBaseFlag_eq_iff q i j false true).mp h).2
  cases hf

theorem markingFirstEdge_ne_mid (i j : Fin q × Bool) (b : Bool) :
    markingFirstEdge q i ≠ markingMidFlag q j b := by
  intro h
  have hs := congrArg (fun e : MarkingSurfaceEdge q => e.1.1.1) h
  change ({markingBaseCell q} : Finset (MarkingSurfaceCell q)) = {markingMidCell q j} at hs
  have he := Finset.singleton_inj.mp hs
  cases he

theorem markingFirstEdge_ne_bed_base (i j : Fin q × Bool) (b : Bool) :
    markingFirstEdge q i ≠ markingBedBaseFlag q j b := by
  intro h
  have hs := congrArg (fun e : MarkingSurfaceEdge q => e.1.1.1) h
  change ({markingBaseCell q} : Finset (MarkingSurfaceCell q)) = {markingBedCell q j b} at hs
  have he := Finset.singleton_inj.mp hs
  cases he

theorem markingFirstEdge_ne_bed_mid (i j : Fin q × Bool) (b : Bool) :
    markingFirstEdge q i ≠ markingBedMidFlag q j b := by
  intro h
  have hs := congrArg (fun e : MarkingSurfaceEdge q => e.1.1.1) h
  change ({markingBaseCell q} : Finset (MarkingSurfaceCell q)) = {markingBedCell q j b} at hs
  have he := Finset.singleton_inj.mp hs
  cases he

/-- No marking's tail uses any distinguished edge, in either orientation. -/
theorem markingTail_avoids_firstEdge (i j : Fin q × Bool)
    (a : MarkingSurfaceEdge q × Bool) (ha : a ∈ markingTail q j) :
    a.1 ≠ markingFirstEdge q i := by
  simp only [markingTail, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (markingFirstEdge_ne_bed_base q i j false).symm
  · exact (markingFirstEdge_ne_bed_mid q i j false).symm
  · exact (markingFirstEdge_ne_mid q i j false).symm
  · exact (markingFirstEdge_ne_mid q i j true).symm
  · exact (markingFirstEdge_ne_bed_mid q i j true).symm
  · exact (markingFirstEdge_ne_bed_base q i j true).symm
  · exact (markingFirstEdge_ne_base_true q i j).symm

theorem markingFirstEdge_not_mem_tail (i j : Fin q × Bool) (b : Bool) :
    (markingFirstEdge q i, b) ∉ markingTail q j := by
  intro h
  exact markingTail_avoids_firstEdge q i j _ h rfl

end FiniteChains.Davis.Genus
