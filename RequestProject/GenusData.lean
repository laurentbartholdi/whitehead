import RequestProject.SurfaceReading
import RequestProject.BlockSurfaceFilling

/-!
# The marked polygon of the closed surface of genus `q`

This file writes down the standard marked polygon of the closed orientable surface of genus `q`
and checks that it is an instance of the data of `RequestProject/SurfacePoset.lean`:

* `FiniteChains.Davis.surfWord a b q` — the surface word
  `∏_{h<q} a_h b_h a_h⁻¹ b_h⁻¹` of the `4q`-gon, and `FiniteChains.Davis.mk_surfWord`, which
  identifies it in the free group with the product of the commutators;
* `FiniteChains.Davis.gvc`, `FiniteChains.Davis.gec` — the identification of the sides of the
  polygon: all `4q` corners become one vertex, the sides are glued in pairs with reversed
  orientation;
* `FiniteChains.Davis.gvlab`, `FiniteChains.Davis.gelb` — the labels, and
  `FiniteChains.Davis.genus_hvlab`, `FiniteChains.Davis.genus_helb`, which say that the boundary
  of the polygon reads the surface word;
* `FiniteChains.Davis.genus_compat` — the identification is consistent with the identification
  of the endpoints of the sides, so the face poset of the surface is a partial order.
-/

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel Cell

section GenusWord

variable {α : Type} (a b : ℕ → α)

/-- The letter at the position `k` of the surface word. -/
def sLet (k : ℕ) : α × Bool :=
  if k % 4 = 0 then (a (k / 4), true)
  else if k % 4 = 1 then (b (k / 4), true)
  else if k % 4 = 2 then (a (k / 4), false)
  else (b (k / 4), false)

/-- **The surface word of genus `n`**: the product of the commutators
`a_h b_h a_h⁻¹ b_h⁻¹`, written out as a list of letters. -/
def surfWord : ℕ → List (α × Bool)
  | 0 => []
  | n + 1 => surfWord n ++ [(a n, true), (b n, true), (a n, false), (b n, false)]

@[simp] theorem surfWord_length (n : ℕ) : (surfWord a b n).length = 4 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [surfWord, ih]; omega

theorem surfWord_getElem? (n k : ℕ) (hk : k < 4 * n) :
    (surfWord a b n)[k]? = some (sLet a b k) := by
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_ge k (4 * n) with hlt | hge
      · have hlen : k < (surfWord a b n).length := by rw [surfWord_length]; exact hlt
        show (surfWord a b n ++ _)[k]? = _
        rw [List.getElem?_append_left hlen]
        exact ih hlt
      · have hlen : (surfWord a b n).length = 4 * n := surfWord_length a b n
        show (surfWord a b n ++
          [(a n, true), (b n, true), (a n, false), (b n, false)])[k]? = _
        rw [List.getElem?_append_right (by omega), hlen]
        have hdiv : k / 4 = n := by omega
        have hk4 : k - 4 * n < 4 := by omega
        interval_cases h : (k - 4 * n)
        · have hmod : k % 4 = 0 := by omega
          simp [sLet, hmod, hdiv]
        · have hmod : k % 4 = 1 := by omega
          simp [sLet, hmod, hdiv]
        · have hmod : k % 4 = 2 := by omega
          simp [sLet, hmod, hdiv]
        · have hmod : k % 4 = 3 := by omega
          simp [sLet, hmod, hdiv]

/-! ### The surface word as a product of commutators -/

/-- The two distinguished generators of the block of the genus `h`. -/
def genLw : ℕ × Bool → List (α × Bool) := fun x => if x.2 then [(b x.1, true)] else [(a x.1, true)]

/-- The list of pairs of distinguished generators of the surface block. -/
def genPairs (n : ℕ) : List ((ℕ × Bool) × (ℕ × Bool)) :=
  (List.range n).map (fun h => ((h, false), (h, true)))

theorem commWord_append {ι G : Type} [Group G] (f : ι → G) (l l' : List (ι × ι)) :
    commWord f (l ++ l') = commWord f l * commWord f l' := by
  simp [commWord, List.prod_append]

/-- **The surface word is the product of the commutators of the distinguished generators.** -/
theorem mk_surfWord (n : ℕ) :
    FreeGroup.mk (surfWord a b n)
      = commWord (fun x => FreeGroup.mk (genLw a b x)) (genPairs n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hrange : List.range (n + 1) = List.range n ++ [n] := by
        simp [List.range_succ]
      have hpairs : genPairs (n + 1) = genPairs n ++ [((n, false), (n, true))] := by
        simp [genPairs, hrange]
      show FreeGroup.mk (surfWord a b n ++
        [(a n, true), (b n, true), (a n, false), (b n, false)]) = _
      rw [← FreeGroup.mul_mk, ih, hpairs, commWord_append]
      congr 1

end GenusWord

/-! ### The identification of the boundary of the polygon -/

section GenusData

variable {α : Type} (a b : ℕ → α) (q : ℕ) [NeZero q]

instance neZero_eight_mul : NeZero (8 * q) := ⟨by have := Nat.pos_of_neZero q; omega⟩

/-- The vertices of the surface: the single corner, and the midpoint of each side. -/
abbrev KVtx : Type := Option (Fin q × Bool)

/-- The edges of the surface: for every pair of identified sides, its two halves. -/
abbrev IEdg : Type := Fin q × Bool × Bool

omit [NeZero q] in
theorem genus_hlt (p : Fin (8 * q)) : p.val / 2 / 4 < q := by
  have := p.isLt
  omega

/-- **The identification of the vertices of the polygon**: all corners become one vertex, the
midpoint of a side is identified with the midpoint of the side paired with it. -/
def gvc (p : Fin (8 * q)) : KVtx q :=
  if p.val % 2 = 0 then none
  else some (⟨p.val / 2 / 4, genus_hlt q p⟩, decide (p.val / 2 % 4 % 2 = 1))

/-- **The identification of the edges of the polygon**: the two sides of a pair are identified
with reversed orientation, so the two halves are exchanged. -/
def gec (p : Fin (8 * q)) : IEdg q :=
  (⟨p.val / 2 / 4, genus_hlt q p⟩, decide (p.val / 2 % 4 % 2 = 1),
    xor (decide (p.val % 2 = 1)) (decide (2 ≤ p.val / 2 % 4)))

/-- The label of a vertex of the surface. -/
def gvlab : KVtx q → Rose α
  | none => Rose.base
  | some (h, i) => Rose.mid (if i then b h.val else a h.val)

/-- The label of an edge of the surface. -/
def gelb : IEdg q → Rose α := fun x => Rose.edg (if x.2.1 then b x.1.val else a x.1.val) x.2.2

omit [NeZero q] in
theorem genus_hM : 8 * q = 2 * (surfWord a b q).length := by
  rw [surfWord_length]; omega

omit [NeZero q] in
/-- **The boundary of the polygon reads the surface word, on the vertices.** -/
theorem genus_hvlab (p : Fin (8 * q)) :
    gvlab a b q (gvc q p) = vertLab (surfWord a b q) p.val := by
  have hlt := p.isLt
  set k := p.val with hk
  by_cases hpar : k % 2 = 0
  · rw [gvc, if_pos hpar]
    rw [vertLab_of_even hpar]
    rfl
  · have hodd : k % 2 = 1 := by omega
    have hs : k / 2 < 4 * q := by omega
    have hget : (surfWord a b q)[k / 2]? = some (sLet a b (k / 2)) :=
      surfWord_getElem? a b q (k / 2) hs
    rw [gvc, if_neg hpar, vertLab_of_odd hodd hget]
    have hr : k / 2 % 4 = 0 ∨ k / 2 % 4 = 1 ∨ k / 2 % 4 = 2 ∨ k / 2 % 4 = 3 := by omega
    show Rose.mid (if (decide (k / 2 % 4 % 2 = 1) : Bool) then b (k / 2 / 4) else a (k / 2 / 4))
      = Rose.mid (sLet a b (k / 2)).1
    rcases hr with h | h | h | h <;> simp [sLet, h]

omit [NeZero q] in
/-- **The boundary of the polygon reads the surface word, on the edges.** -/
theorem genus_helb (p : Fin (8 * q)) :
    gelb a b q (gec q p) = edgeLab (surfWord a b q) p.val := by
  have hlt := p.isLt
  set k := p.val with hk
  have hs : k / 2 < 4 * q := by omega
  have hget : (surfWord a b q)[k / 2]? = some (sLet a b (k / 2)) :=
    surfWord_getElem? a b q (k / 2) hs
  rw [edgeLab_eq hget]
  have hr : k / 2 % 4 = 0 ∨ k / 2 % 4 = 1 ∨ k / 2 % 4 = 2 ∨ k / 2 % 4 = 3 := by omega
  have hpar : k % 2 = 0 ∨ k % 2 = 1 := by omega
  show Rose.edg (if (decide (k / 2 % 4 % 2 = 1) : Bool) then b (k / 2 / 4) else a (k / 2 / 4))
      (xor (decide (k % 2 = 1)) (decide (2 ≤ k / 2 % 4)))
    = Rose.edg (sLet a b (k / 2)).1 (if k % 2 = 0 then !(sLet a b (k / 2)).2
        else (sLet a b (k / 2)).2)
  rcases hr with h | h | h | h <;> rcases hpar with h2 | h2 <;>
    simp [sLet, h, h2]

/-- **The identification is consistent**: two positions of the polygon carrying the same edge of
the surface carry the same pair of endpoints. -/
theorem genus_compat : Compat (gvc q) (gec q) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  -- the three components of the equality of the edge labels
  have h1 : i.val / 2 / 4 = j.val / 2 / 4 := congrArg Fin.val (congrArg Prod.fst hij)
  have h2 : (decide (i.val / 2 % 4 % 2 = 1) : Bool) = decide (j.val / 2 % 4 % 2 = 1) :=
    congrArg (fun x => x.2.1) hij
  have h3 : xor (decide (i.val % 2 = 1)) (decide (2 ≤ i.val / 2 % 4))
      = xor (decide (j.val % 2 = 1)) (decide (2 ≤ j.val / 2 % 4)) :=
    congrArg (fun x => x.2.2) hij
  have h2' : i.val / 2 % 4 % 2 = j.val / 2 % 4 % 2 := by
    by_cases hA : i.val / 2 % 4 % 2 = 1 <;> by_cases hB : j.val / 2 % 4 % 2 = 1 <;>
      simp [hA, hB] at h2 ⊢ <;> omega
  have hsucci : (i + 1).val = (i.val + 1) % (8 * q) := fin_succ_val i
  have hsuccj : (j + 1).val = (j.val + 1) % (8 * q) := fin_succ_val j
  by_cases hsame : i.val / 2 % 4 = j.val / 2 % 4
  · -- the same side of the polygon: the same position
    have hpar : i.val % 2 = j.val % 2 := by
      rw [hsame] at h3
      by_cases hA : i.val % 2 = 1 <;> by_cases hB : j.val % 2 = 1 <;>
        simp [hA, hB] at h3 ⊢
      all_goals omega
    have hij' : i.val = j.val := by omega
    have : i = j := Fin.ext hij'
    subst this
    exact Or.inl ⟨rfl, rfl⟩
  · -- the two paired sides: the positions are mirrored
    have hpar : i.val % 2 ≠ j.val % 2 := by
      intro hp
      rw [hp] at h3
      by_cases hA : 2 ≤ i.val / 2 % 4 <;> by_cases hB : 2 ≤ j.val / 2 % 4 <;>
        simp [hA, hB] at h3 <;> omega
    refine Or.inr ⟨?_, ?_⟩
    · -- `vc i = vc (j+1)`
      rcases Nat.lt_or_ge (i.val % 2) 1 with hI | hI
      · -- `i` is a corner, `j` is a midpoint, so `j+1` is a corner
        have hIe : i.val % 2 = 0 := by omega
        have hJo : j.val % 2 = 1 := by omega
        have hJ1 : (j + 1).val % 2 = 0 := by
          rw [hsuccj]
          rcases Nat.lt_or_ge (j.val + 1) (8 * q) with hlt | hge
          · rw [Nat.mod_eq_of_lt hlt]; omega
          · have : j.val + 1 = 8 * q := by omega
            rw [this, Nat.mod_self]
        rw [gvc, gvc, if_pos hIe, if_pos hJ1]
      · -- `i` is a midpoint, `j` is a corner, so `j+1` is a midpoint of the same pair
        have hIo : i.val % 2 = 1 := by omega
        have hJe : j.val % 2 = 0 := by omega
        have hJlt : j.val + 1 < 8 * q := by omega
        have hJ1v : (j + 1).val = j.val + 1 := by rw [hsuccj, Nat.mod_eq_of_lt hJlt]
        have hJ1o : (j + 1).val % 2 = 1 := by rw [hJ1v]; omega
        have hJ1h : (j + 1).val / 2 = j.val / 2 := by rw [hJ1v]; omega
        rw [gvc, gvc, if_neg (by omega), if_neg (by omega)]
        simp only [Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq, decide_eq_decide]
        omega
    · -- `vc (i+1) = vc j`
      rcases Nat.lt_or_ge (i.val % 2) 1 with hI | hI
      · -- `i+1` is a midpoint of the same pair as `j`
        have hIe : i.val % 2 = 0 := by omega
        have hJo : j.val % 2 = 1 := by omega
        have hIlt : i.val + 1 < 8 * q := by omega
        have hI1v : (i + 1).val = i.val + 1 := by rw [hsucci, Nat.mod_eq_of_lt hIlt]
        have hI1h : (i + 1).val / 2 = i.val / 2 := by rw [hI1v]; omega
        rw [gvc, gvc, if_neg (by omega), if_neg (by omega)]
        simp only [Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq, decide_eq_decide]
        omega
      · -- `i+1` is a corner, and so is `j`
        have hIo : i.val % 2 = 1 := by omega
        have hJe : j.val % 2 = 0 := by omega
        have hI1 : (i + 1).val % 2 = 0 := by
          rw [hsucci]
          rcases Nat.lt_or_ge (i.val + 1) (8 * q) with hlt | hge
          · rw [Nat.mod_eq_of_lt hlt]; omega
          · have : i.val + 1 = 8 * q := by omega
            rw [this, Nat.mod_self]
        rw [gvc, gvc, if_pos hI1, if_pos hJe]

end GenusData

end Davis
end FiniteChains
