module

public import RequestProject.GenusLoops
public import RequestProject.BarycentricCocycleDescent

@[expose] public section

/-! Exact boundary incidences and cocycle values of the genuine marked loops. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Cell
variable (q : ℕ) [NeZero q]

def markedBoundaryPos (x : Fin q × Bool) (b : Bool) : Fin (8 * q) :=
  ⟨8 * x.1.val + (if x.2 then 2 else 0) + (if b then 1 else 0), by
    have := x.1.isLt
    cases x.2 <;> cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩

omit [NeZero q] in
theorem markedBoundaryPos_div (x : Fin q × Bool) (b : Bool) :
    (markedBoundaryPos q x b).val / 2 / 4 = x.1.val := by
  obtain ⟨h, t⟩ := x
  cases t <;> cases b <;> simp only [markedBoundaryPos, Bool.false_eq_true, ↓reduceIte] <;> omega

omit [NeZero q] in
theorem markedBoundaryPos_mod (x : Fin q × Bool) (b : Bool) :
    (markedBoundaryPos q x b).val / 2 % 4 = if x.2 then 1 else 0 := by
  obtain ⟨h, t⟩ := x
  cases t <;> cases b <;> simp only [markedBoundaryPos, Bool.false_eq_true, ↓reduceIte] <;> omega

omit [NeZero q] in
theorem markedBoundaryPos_par (x : Fin q × Bool) (b : Bool) :
    (markedBoundaryPos q x b).val % 2 = if b then 1 else 0 := by
  obtain ⟨h, t⟩ := x
  cases t <;> cases b <;> simp only [markedBoundaryPos, Bool.false_eq_true, ↓reduceIte] <;> omega

omit [NeZero q] in
theorem gvc_markedBoundaryPos_false (x : Fin q × Bool) :
    gvc q (markedBoundaryPos q x false) = none := by
  rw [gvc, markedBoundaryPos_par]
  rfl

omit [NeZero q] in
theorem gvc_markedBoundaryPos_true (x : Fin q × Bool) :
    gvc q (markedBoundaryPos q x true) = some x := by
  rw [gvc, markedBoundaryPos_par]
  simp only [↓reduceIte, Nat.one_ne_zero]
  apply congrArg some
  apply Prod.ext
  · apply Fin.ext
    exact markedBoundaryPos_div q x true
  · rw [markedBoundaryPos_mod]
    cases x.2 <;> rfl

omit [NeZero q] in
theorem gec_markedBoundaryPos (x : Fin q × Bool) (b : Bool) :
    gec q (markedBoundaryPos q x b) = (x.1, x.2, b) := by
  apply Prod.ext
  · apply Fin.ext
    exact markedBoundaryPos_div q x b
  · change (decide ((markedBoundaryPos q x b).val / 2 % 4 % 2 = 1),
      xor (decide ((markedBoundaryPos q x b).val % 2 = 1))
        (decide (2 ≤ (markedBoundaryPos q x b).val / 2 % 4))) = (x.2, b)
    rw [markedBoundaryPos_mod, markedBoundaryPos_par]
    cases x.2 <;> cases b <;> rfl

theorem markedBoundaryPos_succ (x : Fin q × Bool) :
    markedBoundaryPos q x false + 1 = markedBoundaryPos q x true := by
  apply Fin.ext
  rw [fin_succ_val]
  have ht := (markedBoundaryPos q x true).isLt
  change (8 * x.1.val + (if x.2 then 2 else 0) + 0 + 1) % (8 * q) =
    8 * x.1.val + (if x.2 then 2 else 0) + 1
  change 8 * x.1.val + (if x.2 then 2 else 0) + 1 < 8 * q at ht
  simpa only [add_zero] using Nat.mod_eq_of_lt ht

theorem gvc_markedBoundaryPos_end (x : Fin q × Bool) :
    gvc q (markedBoundaryPos q x true + 1) = none := by
  rw [gvc, if_pos]
  rw [fin_succ_val]
  have ht : (markedBoundaryPos q x true).val + 1 < 8 * q := by
    obtain ⟨h, t⟩ := x
    have := h.isLt
    cases t <;> simp only [markedBoundaryPos, Bool.false_eq_true, ↓reduceIte] <;> omega
  rw [Nat.mod_eq_of_lt ht]
  have hpar : (markedBoundaryPos q x true).val % 2 = 1 := markedBoundaryPos_par q x true
  omega

omit [NeZero q] in
theorem gvc_endpoint (p : Fin (8 * q)) :
    gvc q p = none ∨ gvc q p = some ((gec q p).1, (gec q p).2.1) := by
  unfold gvc
  split_ifs with hp
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem gvc_succ_endpoint (p : Fin (8 * q)) :
    gvc q (p + 1) = none ∨ gvc q (p + 1) = some ((gec q p).1, (gec q p).2.1) := by
  have ht := p.isLt
  have hv := fin_succ_val p
  by_cases he : (p + 1).val % 2 = 0
  · exact Or.inl (by rw [gvc, if_pos he])
  · have hs : (p + 1).val = p.val + 1 := by
      rw [hv]
      apply Nat.mod_eq_of_lt
      by_contra hn
      have hn' : p.val + 1 = 8 * q := by omega
      rw [hv, hn', Nat.mod_self] at he
      exact he rfl
    have hp : p.val % 2 = 0 := by omega
    apply Or.inr
    rw [gvc, if_neg he]
    apply congrArg some
    apply Prod.ext
    · apply Fin.ext
      change (p + 1).val / 2 / 4 = p.val / 2 / 4
      omega
    · change decide ((p + 1).val / 2 % 4 % 2 = 1) = decide (p.val / 2 % 4 % 2 = 1)
      have hhalf : (p + 1).val / 2 = p.val / 2 := by omega
      rw [hhalf]

theorem gSig_boundary_path (x : Fin q × Bool) :
    gSig q (x.1.val, x.2) =
      bdEdge (gc q) (markedBoundaryPos q x false) ++ bdEdge (gc q) (markedBoundaryPos q x true) := by
  rw [gSig, Nat.mod_eq_of_lt x.1.isLt]
  change pPath (gc q) (8 * x.1.val + (if x.2 then 2 else 0)) = _
  rw [pPath_eq]
  have h₀ : cyc (8 * q) (8 * x.1.val + (if x.2 then 2 else 0)) =
      markedBoundaryPos q x false := by
    apply Fin.ext
    have ht := (markedBoundaryPos q x false).isLt
    simpa only [cyc, markedBoundaryPos, Bool.false_eq_true, ↓reduceIte, add_zero] using
      Nat.mod_eq_of_lt ht
  have h₁ : cyc (8 * q) (8 * x.1.val + (if x.2 then 2 else 0) + 1) =
      markedBoundaryPos q x true := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt (markedBoundaryPos q x true).isLt
  rw [h₀, h₁]

universe v
variable {G : Type v} [Group G]
  (c : OrdCocycle (NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q)))) G)

theorem read_bdEdge (p : Fin (8 * q)) :
    c.readPath (bdEdge (gc q) p) =
      (barycentricCocycle c).val (cV (gc q) p) (cE (gc q) p) *
        ((barycentricCocycle c).val (cV (gc q) (p + 1)) (cE (gc q) p))⁻¹ := by
  rw [bdEdge, OrdCocycle.readPath_append, ← revPath_edgeHop, OrdCocycle.readPath_revPath,
    barycentricCocycle_val c (cV_le_cE (gc q) p),
    barycentricCocycle_val c (cV1_le_cE (gc q) p)]

def boundaryMarkValue (d : OrdCocycle (SCell (gvc q) (gec q) (gc q)) G) (x : Fin q × Bool) : G :=
  d.val (.vtx none) (.bed (x.1, x.2, false)) *
    (d.val (.vtx (some x)) (.bed (x.1, x.2, false)))⁻¹ *
    (d.val (.vtx (some x)) (.bed (x.1, x.2, true)) *
      (d.val (.vtx none) (.bed (x.1, x.2, true)))⁻¹)

theorem read_gSig_boundaryMarkValue (x : Fin q × Bool) :
    c.readPath (gSig q (x.1.val, x.2)) = boundaryMarkValue q (barycentricCocycle c) x := by
  rw [gSig_boundary_path, OrdCocycle.readPath_append, read_bdEdge, read_bdEdge,
    markedBoundaryPos_succ]
  simp only [cV, cE, gvc_markedBoundaryPos_false, gvc_markedBoundaryPos_true,
    gvc_markedBoundaryPos_end, gec_markedBoundaryPos, boundaryMarkValue, toS]

end FiniteChains.Davis.Genus
