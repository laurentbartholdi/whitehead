import RequestProject.SurfaceLink
import RequestProject.GenusLoops

/-!
# The nerve of the block of genus `q` is a closed surface

`RequestProject/GenusData.lean` writes down the `4q`-gon whose sides are glued in pairs
according to the surface word `∏_{h<q} a_h b_h a_h⁻¹ b_h⁻¹`, and
`RequestProject/GenusApply.lean` uses the comparability graph of its face poset as the nerve of
the block.  This file checks that this nerve really is a triangulation of a **closed** surface:

* `FiniteChains.Davis.genus_polygonData` — the sides are glued in pairs, no side becomes a loop,
  and every vertex and every edge of the surface occurs;
* `FiniteChains.Davis.genus_cornersConnected` — the `4q` corners of the polygon, which are all
  identified to one vertex, are glued in a **single** cycle, and the two midpoints of a pair of
  identified sides are glued to each other;
* `FiniteChains.Davis.genusClosedSurface` — hence the face poset is a closed surface cell
  structure, so the nerve is a flag triangulation of a closed surface;
* `FiniteChains.Davis.genus_edgeInTwoTriangles` — in particular every edge of the triangulation
  lies in exactly two triangles, the hypothesis used by the collapse of
  `RequestProject/SurfaceBlockCollapse.lean`.

Together with `FiniteChains.Davis.genus_euler_characteristic` (the alternating sum of the numbers
of cells is `2 - 2q`) this identifies the surface as the closed orientable surface of genus `q`.

The corner walk is the classical one: writing the positions of the boundary of the `4q`-gon as
`8h + 2t` with `t < 4` (each side of the polygon is cut into two positions), the side going out
of the corner `8h` is glued to the side coming into the corner `8h + 6`, then `8h + 6` to
`8h + 4`, then `8h + 4` to `8h + 2`, and finally `8h + 2` to the corner `8(h+1)` of the next
commutator.  So all `4q` corners lie on one cycle.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Davis

open Cell ASC Relation Genus

section GenusSurface

variable (q : ℕ) [NeZero q]

/-! ### Reading the labels -/

omit [NeZero q] in
/-- Two positions of the boundary carry the same edge of the surface exactly when they agree on
the commutator, on the letter, and on the half of the side. -/
theorem gec_eq_iff' (m n : Fin (8 * q)) :
    gec q m = gec q n ↔
      (m.val / 2 / 4 = n.val / 2 / 4 ∧
        m.val / 2 % 4 % 2 = n.val / 2 % 4 % 2 ∧
        (m.val % 2 + (if 2 ≤ m.val / 2 % 4 then 1 else 0)) % 2
          = (n.val % 2 + (if 2 ≤ n.val / 2 % 4 then 1 else 0)) % 2) := by
  have hm2 : m.val % 2 = 0 ∨ m.val % 2 = 1 := by omega
  have hn2 : n.val % 2 = 0 ∨ n.val % 2 = 1 := by omega
  by_cases h2 : 2 ≤ m.val / 2 % 4 <;> by_cases h4 : 2 ≤ n.val / 2 % 4 <;>
    rcases hm2 with h1 | h1 <;> rcases hn2 with h3 | h3 <;>
    simp [gec, Prod.ext_iff, Fin.ext_iff, decide_eq_decide, h1, h2, h3, h4] <;> omega

omit [NeZero q] in
/-- An even position of the boundary is a corner of the polygon. -/
theorem gvc_even {p : Fin (8 * q)} (h : p.val % 2 = 0) : gvc q p = none := by
  rw [gvc, if_pos h]

omit [NeZero q] in
/-- An odd position of the boundary is the midpoint of a side. -/
theorem gvc_odd {p : Fin (8 * q)} (h : p.val % 2 ≠ 0) :
    gvc q p = some (⟨p.val / 2 / 4, genus_hlt q p⟩, decide (p.val / 2 % 4 % 2 = 1)) := by
  rw [gvc, if_neg h]

theorem fpred_val_pos {n : Fin (8 * q)} {a : ℕ} (hv : n.val = a) (hpos : 0 < a) :
    (fpred n).val = a - 1 := by
  rw [fpred_val, hv, if_neg (by omega)]

/-! ### The polygon data of the surface of genus `q` -/

theorem genus_pairs : EdgePairs (gec q) := by
  intro i
  have hq := Nat.pos_of_neZero q
  have hi := i.isLt
  have hh : i.val / 2 / 4 < q := by omega
  have hmlt : 8 * (i.val / 2 / 4) + 2 * (if i.val / 2 % 4 < 2 then i.val / 2 % 4 + 2
      else i.val / 2 % 4 - 2) + (1 - i.val % 2) < 8 * q := by
    split_ifs <;> omega
  refine ⟨⟨_, hmlt⟩, ?_, ?_, ?_⟩
  · rw [Ne, Fin.ext_iff]
    simp only []
    split_ifs <;> omega
  · rw [gec_eq_iff']
    refine ⟨?_, ?_, ?_⟩ <;> simp only [] <;> split_ifs <;> omega
  · intro k hk
    rw [gec_eq_iff'] at hk
    obtain ⟨h1, h2, h3⟩ := hk
    have hk8 := k.isLt
    rw [Fin.ext_iff, Fin.ext_iff]
    simp only []
    split_ifs at h3 ⊢ <;> omega

theorem genus_noLoop : NoLoopSide (gvc q) := by
  intro p
  have hq := Nat.pos_of_neZero q
  have hp := p.isLt
  have hs : (p + 1).val = (p.val + 1) % (8 * q) := fin_succ_val p
  have hpar : (p + 1).val % 2 = (p.val + 1) % 2 := by
    rw [hs]
    rcases Nat.lt_or_ge (p.val + 1) (8 * q) with h | h
    · rw [Nat.mod_eq_of_lt h]
    · have he : p.val + 1 = 8 * q := by omega
      rw [he, Nat.mod_self]
      omega
  by_cases h : p.val % 2 = 0
  · rw [gvc, if_pos h, gvc, if_neg (by omega)]
    simp
  · rw [gvc, if_neg h, gvc, if_pos (by omega)]
    simp

theorem genus_vc_surj : Function.Surjective (gvc q) := by
  have hq := Nat.pos_of_neZero q
  rintro (_ | ⟨h, i⟩)
  · exact ⟨⟨0, by omega⟩, by rw [gvc]; simp⟩
  · have hh := h.isLt
    refine ⟨⟨2 * (4 * h.val + (if i then 1 else 0)) + 1, by split_ifs <;> omega⟩, ?_⟩
    have hval : (⟨2 * (4 * h.val + (if i then 1 else 0)) + 1, by split_ifs <;> omega⟩ :
        Fin (8 * q)).val = 2 * (4 * h.val + (if i then 1 else 0)) + 1 := rfl
    rw [gvc, if_neg (by rw [hval]; split_ifs <;> omega)]
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · apply Fin.ext
      show (2 * (4 * h.val + (if i then 1 else 0)) + 1) / 2 / 4 = h.val
      split_ifs <;> omega
    · have e2 : (2 * (4 * h.val + (if i then 1 else 0)) + 1) / 2 % 4 % 2
          = (if i then 1 else 0) := by
        split_ifs <;> omega
      show decide ((2 * (4 * h.val + (if i then 1 else 0)) + 1) / 2 % 4 % 2 = 1) = i
      rw [e2]
      cases i <;> simp

theorem genus_ec_surj : Function.Surjective (gec q) := by
  have hq := Nat.pos_of_neZero q
  rintro ⟨h, i, b⟩
  have hh := h.isLt
  refine ⟨⟨2 * (4 * h.val + (if i then 1 else 0)) + (if b then 1 else 0), by
    split_ifs <;> omega⟩, ?_⟩
  have e1 : (2 * (4 * h.val + (if i then 1 else 0)) + (if b then 1 else 0)) / 2 / 4 = h.val := by
    split_ifs <;> omega
  have e2 : (2 * (4 * h.val + (if i then 1 else 0)) + (if b then 1 else 0)) / 2 % 4 =
      (if i then 1 else 0) := by
    split_ifs <;> omega
  have e3 : (2 * (4 * h.val + (if i then 1 else 0)) + (if b then 1 else 0)) % 2 =
      (if b then 1 else 0) := by
    split_ifs <;> omega
  simp only [gec, Prod.mk.injEq]
  refine ⟨Fin.ext ?_, ?_, ?_⟩
  · show (2 * (4 * h.val + (if i then 1 else 0)) + (if b then 1 else 0)) / 2 / 4 = h.val
    exact e1
  · show decide ((2 * (4 * h.val + (if i then 1 else 0)) + (if b then 1 else 0)) / 2 % 4 % 2 = 1)
      = i
    rw [e2]
    cases i <;> simp
  · show (decide ((2 * (4 * h.val + (if i then 1 else 0)) + (if b then 1 else 0)) % 2 = 1) ^^
      decide (2 ≤ (2 * (4 * h.val + (if i then 1 else 0)) + (if b then 1 else 0)) / 2 % 4)) = b
    rw [e2, e3]
    cases i <;> cases b <;> simp

/-- **The identification of the boundary of the `4q`-gon is a polygon gluing**: the sides are
glued in pairs, no side becomes a loop, and every vertex and every edge occurs. -/
theorem genus_polygonData : PolygonData (gvc q) (gec q) where
  three_le := by have := Nat.pos_of_neZero q; omega
  pairs := genus_pairs q
  noLoop := genus_noLoop q
  vc_surj := genus_vc_surj q
  ec_surj := genus_ec_surj q

/-! ### The corners of the polygon form one cycle -/

/-- Two positions of the boundary are corners at the same vertex sharing a side, when the side
going out of the first is glued to the side coming into the second. -/
theorem cornerAdj_of_vals {m n : Fin (8 * q)} {a b : ℕ} (hvc : gvc q m = gvc q n)
    (ha : m.val = a) (hb : (fpred n).val = b)
    (h1 : a / 2 / 4 = b / 2 / 4) (h2 : a / 2 % 4 % 2 = b / 2 % 4 % 2)
    (h3 : (a % 2 + (if 2 ≤ a / 2 % 4 then 1 else 0)) % 2
        = (b % 2 + (if 2 ≤ b / 2 % 4 then 1 else 0)) % 2) :
    CornerAdj (gvc q) (gec q) m n := by
  refine ⟨hvc, Or.inr (Or.inl ((gec_eq_iff' q m (fpred n)).2 ?_))⟩
  rw [ha, hb]
  exact ⟨h1, h2, h3⟩

theorem cornerAdj_step1 (h : ℕ) (hh : h < q) :
    CornerAdj (gvc q) (gec q) ⟨8 * h, by omega⟩ ⟨8 * h + 6, by omega⟩ := by
  refine cornerAdj_of_vals q (a := 8 * h) (b := 8 * h + 5)
    (by rw [gvc_even q (by simp; omega), gvc_even q (by simp; omega)]) rfl
    (fpred_val_pos q (a := 8 * h + 6) rfl (by omega)) (by omega) (by omega) ?_
  rw [if_neg (by omega), if_pos (by omega)]
  omega

theorem cornerAdj_step2 (h : ℕ) (hh : h < q) :
    CornerAdj (gvc q) (gec q) ⟨8 * h + 6, by omega⟩ ⟨8 * h + 4, by omega⟩ := by
  refine cornerAdj_of_vals q (a := 8 * h + 6) (b := 8 * h + 3)
    (by rw [gvc_even q (by simp; omega), gvc_even q (by simp; omega)]) rfl
    (fpred_val_pos q (a := 8 * h + 4) rfl (by omega)) (by omega) (by omega) ?_
  rw [if_pos (by omega), if_neg (by omega)]
  omega

theorem cornerAdj_step3 (h : ℕ) (hh : h < q) :
    CornerAdj (gvc q) (gec q) ⟨8 * h + 4, by omega⟩ ⟨8 * h + 2, by omega⟩ := by
  refine cornerAdj_of_vals q (a := 8 * h + 4) (b := 8 * h + 1)
    (by rw [gvc_even q (by simp; omega), gvc_even q (by simp; omega)]) rfl
    (fpred_val_pos q (a := 8 * h + 2) rfl (by omega)) (by omega) (by omega) ?_
  rw [if_pos (by omega), if_neg (by omega)]
  omega

theorem cornerAdj_step4 (h : ℕ) (hh : h + 1 < q) :
    CornerAdj (gvc q) (gec q) ⟨8 * h + 2, by omega⟩ ⟨8 * (h + 1), by omega⟩ := by
  refine cornerAdj_of_vals q (a := 8 * h + 2) (b := 8 * h + 7)
    (by rw [gvc_even q (by simp; omega), gvc_even q (by simp; omega)]) rfl
    (fpred_val_pos q (a := 8 * (h + 1)) rfl (by omega)) (by omega) (by omega) ?_
  rw [if_neg (by omega), if_pos (by omega)]
  omega

/-- Inside one commutator all four corners of the polygon are joined. -/
theorem conn_within_block (h : ℕ) (hh : h < q) (t : ℕ) (ht : t < 4) :
    ReflTransGen (CornerAdj (gvc q) (gec q)) ⟨8 * h, by omega⟩ ⟨8 * h + 2 * t, by omega⟩ := by
  have e1 := ReflTransGen.single (cornerAdj_step1 q h hh)
  have e2 := e1.tail (cornerAdj_step2 q h hh)
  have e3 := e2.tail (cornerAdj_step3 q h hh)
  interval_cases t
  · simpa using ReflTransGen.refl
  · simpa using e3
  · simpa using e2
  · simpa using e1

/-- **The corner `8h` of every commutator is joined to the corner `0`.** -/
theorem conn_block_zero (h : ℕ) (hh : h < q) :
    ReflTransGen (CornerAdj (gvc q) (gec q)) ⟨0, by have := Nat.pos_of_neZero q; omega⟩
      ⟨8 * h, by omega⟩ := by
  induction h with
  | zero => simpa using ReflTransGen.refl
  | succ n ih =>
      have hn : n < q := by omega
      have h1 := ih hn
      have h2 := conn_within_block q n hn 1 (by omega)
      have h3 := ReflTransGen.single (cornerAdj_step4 q n (by omega))
      have h2' : ReflTransGen (CornerAdj (gvc q) (gec q)) (⟨8 * n, by omega⟩ : Fin (8 * q))
          ⟨8 * n + 2, by omega⟩ := by simpa using h2
      exact (h1.trans h2').trans h3

/-- Every corner of the polygon is joined to the corner `0`. -/
theorem conn_even_zero (p : Fin (8 * q)) (hp : p.val % 2 = 0) :
    ReflTransGen (CornerAdj (gvc q) (gec q)) ⟨0, by have := Nat.pos_of_neZero q; omega⟩ p := by
  have hq := Nat.pos_of_neZero q
  have hlt := p.isLt
  have hh : p.val / 8 < q := by omega
  have hblock := conn_block_zero q (p.val / 8) hh
  have hwithin := conn_within_block q (p.val / 8) hh (p.val % 8 / 2) (by omega)
  have hval : (⟨8 * (p.val / 8) + 2 * (p.val % 8 / 2), by omega⟩ : Fin (8 * q)) = p := by
    apply Fin.ext
    simp only []
    omega
  rw [hval] at hwithin
  exact hblock.trans hwithin

/-- **The corners of the `4q`-gon are glued in a single cycle**, and the two midpoints of a pair
of identified sides are glued to each other. -/
theorem genus_cornersConnected : CornersConnected (gvc q) (gec q) := by
  have hq := Nat.pos_of_neZero q
  intro i j hij
  have hi8 := i.isLt
  have hj8 := j.isLt
  by_cases hi : i.val % 2 = 0
  · -- both positions are corners of the polygon
    have hj : j.val % 2 = 0 := by
      by_contra hj
      rw [gvc_even q hi, gvc_odd q hj] at hij
      simp at hij
    letI : Std.Symm (CornerAdj (gvc q) (gec q)) := ⟨fun _ _ h => cornerAdj_symm h⟩
    exact (ReflTransGen.stdSymm.symm _ _ (conn_even_zero q i hi)).trans
      (conn_even_zero q j hj)
  · -- both positions are midpoints of sides
    have hj : j.val % 2 ≠ 0 := by
      intro hj
      rw [gvc_even q hj, gvc_odd q hi] at hij
      simp at hij
    rw [gvc_odd q hi, gvc_odd q hj] at hij
    simp only [Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq, decide_eq_decide] at hij
    obtain ⟨h1, h2⟩ := hij
    have h2' : i.val / 2 % 4 % 2 = j.val / 2 % 4 % 2 := by
      by_cases ha : i.val / 2 % 4 % 2 = 1 <;> by_cases hb : j.val / 2 % 4 % 2 = 1 <;>
        simp [ha, hb] at h2 ⊢ <;> omega
    by_cases heq : i.val = j.val
    · have hijeq : i = j := Fin.ext heq
      rw [hijeq]
    -- the two positions are the midpoints of a pair of glued sides
    rcases Nat.lt_or_ge (i.val / 2 % 4) 2 with hr | hr
    · have hjv : j.val = i.val + 4 := by omega
      refine ReflTransGen.single ?_
      refine cornerAdj_of_vals q (a := i.val) (b := i.val + 3)
        (by rw [gvc_odd q hi, gvc_odd q hj]
            simp only [Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq, decide_eq_decide]
            exact ⟨h1, by omega⟩) rfl
        (by rw [fpred_val_pos q (a := j.val) rfl (by omega)]; omega) (by omega) (by omega) ?_
      rw [if_neg (by omega), if_pos (by omega)]
      omega
    · have hjv : j.val = i.val - 4 := by omega
      refine ReflTransGen.single (cornerAdj_symm ?_)
      refine cornerAdj_of_vals q (a := j.val) (b := j.val + 3)
        (by rw [gvc_odd q hi, gvc_odd q hj]
            simp only [Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq, decide_eq_decide]
            exact ⟨h1.symm, by omega⟩) rfl
        (by rw [fpred_val_pos q (a := i.val) rfl (by omega)]; omega) (by omega) (by omega) ?_
      rw [if_neg (by omega), if_pos (by omega)]
      omega

/-! ### The closed surface -/

/-- **The nerve of the block of genus `q` is a closed surface.** -/
def genusClosedSurface : ClosedSurfacePoset (SCell (gvc q) (gec q) (gc q)) :=
  closedSurfacePoset_SCell (gc q) (genus_polygonData q) (genus_cornersConnected q)

/-- **Every edge of the triangulation of the surface of genus `q` lies in exactly two
triangles.** -/
theorem genus_edgeInTwoTriangles :
    EdgeInTwoTriangles (orderComplex (SCell (gvc q) (gec q) (gc q))) :=
  (genusClosedSurface q).toSurfaceRank.edgeInTwoTriangles

/-- The triangulation of the surface of genus `q` is two-dimensional. -/
theorem genus_chain_card_le_three {s : Finset (SCell (gvc q) (gec q) (gc q))}
    (hs : s ∈ (orderComplex (SCell (gvc q) (gec q) (gc q))).faces) : s.card ≤ 3 :=
  (genusClosedSurface q).toSurfaceRank.chain_card_le_three hs

end GenusSurface

end Davis
end FiniteChains
