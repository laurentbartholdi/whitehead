import RequestProject.BlockConnected

/-!
# A concrete attaching map: the cycle that spells a prescribed word

Everything in `RequestProject/BlockSpinePres.lean` and `RequestProject/BlockSpineSubst.lean` is
stated for an arbitrary nerve `L` and an arbitrary attaching map
`att : NeSpx A →o presModelPos ρ`.  This file produces such an `att` **concretely**, together
with the geometric loop of the cut surface along which it spells a prescribed word.

The nerve is the cycle `C_M` with `M = 2·|u|` vertices, `u` being the prescribed word: its
vertices alternate between *corner* vertices (even positions) and *midpoints of letters* (odd
positions), and its edges are the two halves of the letters.  The attaching map is the simplicial
map onto the subdivided rose of `RequestProject/PresPosetModel.lean` which sends a vertex and an
edge to the cell carrying the same label; going once around the cycle therefore spells exactly
the word `u`.

This file contains the combinatorial part: the cycle, its labels, the attaching map and its
monotonicity.  The loop and the application of the theorem are in
`RequestProject/AttCycleLoop.lean` and `RequestProject/AttCycleApply.lean`.
-/

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel

universe u

/-! ### The cycle graph -/

/-- Adjacency in the cycle on `Fin M`: consecutive positions, and the wrap-around pair. -/
def cycAdj (M : ℕ) (i j : Fin M) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
    (i.val = 0 ∧ j.val + 1 = M) ∨ (j.val = 0 ∧ i.val + 1 = M)

/-- **The cycle `C_M` as a nerve**: the commutation graph whose graph is a cycle of length `M`. -/
def cycRel (M : ℕ) (hM : 4 ≤ M) : CommRel (Fin M) where
  rel := cycAdj M
  rel_symm := by
    intro a b h
    simp only [cycAdj] at h ⊢
    tauto
  rel_irrefl := by
    intro a h
    simp only [cycAdj] at h
    have := a.isLt
    omega

theorem cycRel_rel_iff {M : ℕ} (hM : 4 ≤ M) (i j : Fin M) :
    (cycRel M hM).rel i j ↔ cycAdj M i j := Iff.rfl

/-- The cycle has no triangles, so all its simplices are vertices and edges. -/
theorem card_le_two_of_isSimplex {M : ℕ} (hM : 4 ≤ M) {σ : Finset (Fin M)}
    (h : IsSimplex (cycRel M hM) σ) : σ.card ≤ 2 := by
  by_contra hc
  obtain ⟨a, b, c, ha, hb, hc', hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 (not_le.1 hc)
  have h1 := h a ha b hb hab
  have h2 := h a ha c hc' hac
  have h3 := h b hb c hc' hbc
  simp only [cycRel, cycAdj] at h1 h2 h3
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hac' : a.val ≠ c.val := fun h => hac (Fin.ext h)
  have hbc' : b.val ≠ c.val := fun h => hbc (Fin.ext h)
  have := a.isLt
  have := b.isLt
  have := c.isLt
  omega

/-! ### The labels -/

section Labels

variable {α : Type u}

/-- The label of the vertex at the position `p` of the cycle: even positions are corners of the
word and carry the base vertex of the rose, odd positions are midpoints of letters and carry the
midpoint of the loop of the corresponding generator. -/
def vertLab (l : List (α × Bool)) (p : ℕ) : Rose α :=
  if p % 2 = 0 then Rose.base
  else
    match l[p / 2]? with
    | some q => Rose.mid q.1
    | none => Rose.base

/-- The label of the edge joining the positions `p` and `p+1` of the cycle: the first half of the
letter `p/2` for even `p`, its second half for odd `p`, the halves being taken in the order
prescribed by the sign of the letter. -/
def edgeLab (l : List (α × Bool)) (p : ℕ) : Rose α :=
  match l[p / 2]? with
  | some q => Rose.edg q.1 (if p % 2 = 0 then !q.2 else q.2)
  | none => Rose.base

@[simp] theorem vertLab_of_even {l : List (α × Bool)} {p : ℕ} (hp : p % 2 = 0) :
    vertLab l p = Rose.base := if_pos hp

theorem vertLab_of_odd {l : List (α × Bool)} {p : ℕ} {q : α × Bool} (hp : p % 2 = 1)
    (hq : l[p / 2]? = some q) : vertLab l p = Rose.mid q.1 := by
  simp [vertLab, hp, hq]

theorem edgeLab_eq {l : List (α × Bool)} {p : ℕ} {q : α × Bool} (hq : l[p / 2]? = some q) :
    edgeLab l p = Rose.edg q.1 (if p % 2 = 0 then !q.2 else q.2) := by
  simp [edgeLab, hq]

theorem getElem?_half {l : List (α × Bool)} {p : ℕ} (hp : p < 2 * l.length) :
    ∃ q, l[p / 2]? = some q :=
  ⟨l[p / 2]'(by omega), List.getElem?_eq_getElem (by omega)⟩

/-- The vertex at a position lies under the edge that starts at it. -/
theorem vertLab_le_edgeLab {l : List (α × Bool)} {p : ℕ} (hp : p < 2 * l.length) :
    vertLab l p ≤ edgeLab l p := by
  obtain ⟨q, hq⟩ := getElem?_half hp
  rcases Nat.even_or_odd p with he | ho
  · have h0 : p % 2 = 0 := Nat.even_iff.1 he
    rw [vertLab_of_even h0, edgeLab_eq hq]
    exact Rose.base_le_edg _ _
  · have h1 : p % 2 = 1 := Nat.odd_iff.1 ho
    rw [vertLab_of_odd h1 hq, edgeLab_eq hq, if_neg (by omega)]
    exact Rose.mid_le_edg _ _

/-- The vertex at the next position lies under the same edge. -/
theorem vertLab_succ_le_edgeLab {l : List (α × Bool)} {p : ℕ} (hp : p + 1 < 2 * l.length) :
    vertLab l (p + 1) ≤ edgeLab l p := by
  obtain ⟨q, hq⟩ := getElem?_half (Nat.lt_of_succ_lt hp)
  rcases Nat.even_or_odd p with he | ho
  · have h0 : p % 2 = 0 := Nat.even_iff.1 he
    have hhalf : (p + 1) / 2 = p / 2 := by omega
    rw [vertLab_of_odd (q := q) (by omega) (by rw [hhalf]; exact hq), edgeLab_eq hq,
      if_pos h0]
    exact Rose.mid_le_edg _ _
  · have h1 : p % 2 = 1 := Nat.odd_iff.1 ho
    rw [vertLab_of_even (by omega), edgeLab_eq hq]
    exact Rose.base_le_edg _ _

/-- Every edge of the cycle carries a one-cell of the rose, so the base vertex lies under it. -/
theorem base_le_edgeLab {l : List (α × Bool)} {p : ℕ} (hp : p < 2 * l.length) :
    (Rose.base : Rose α) ≤ edgeLab l p := by
  obtain ⟨q, hq⟩ := getElem?_half hp
  rw [edgeLab_eq hq]
  exact Rose.base_le_edg _ _

/-! ### The label of a simplex -/

/-- The position of the edge with endpoints at the positions `a < b`: the pair is either a pair
of consecutive positions, or the wrap-around pair `{0, M-1}`, which is the edge starting at
`M-1`. -/
def edgePos (a b : ℕ) : ℕ := if b = a + 1 then a else b

/-- **The label of a simplex of the cycle**: a vertex carries the label of its position, an edge
the label of its position. -/
def roseLab (l : List (α × Bool)) {M : ℕ} (σ : Finset (Fin M)) : Rose α :=
  if h : σ.Nonempty then
    if σ.card = 1 then vertLab l (σ.min' h).val
    else edgeLab l (edgePos (σ.min' h).val (σ.max' h).val)
  else Rose.base

@[simp] theorem roseLab_singleton (l : List (α × Bool)) {M : ℕ} (v : Fin M) :
    roseLab l ({v} : Finset (Fin M)) = vertLab l v.val := by
  have h : ({v} : Finset (Fin M)).Nonempty := ⟨v, by simp⟩
  simp [roseLab, h]

theorem pair_min' {M : ℕ} {x y : Fin M} (hxy : x < y) (h : ({x, y} : Finset (Fin M)).Nonempty) :
    ({x, y} : Finset (Fin M)).min' h = x := by
  refine le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ ?_)
  intro b hb
  rcases Finset.mem_insert.1 hb with rfl | hb
  · exact le_refl _
  · rw [Finset.mem_singleton] at hb
    exact hb ▸ le_of_lt hxy

theorem pair_max' {M : ℕ} {x y : Fin M} (hxy : x < y) (h : ({x, y} : Finset (Fin M)).Nonempty) :
    ({x, y} : Finset (Fin M)).max' h = y := by
  refine le_antisymm (Finset.max'_le _ _ _ ?_) (Finset.le_max' _ _ (by simp))
  intro b hb
  rcases Finset.mem_insert.1 hb with rfl | hb
  · exact le_of_lt hxy
  · rw [Finset.mem_singleton] at hb
    exact hb ▸ le_refl _

theorem roseLab_pair (l : List (α × Bool)) {M : ℕ} {x y : Fin M} (hxy : x < y) :
    roseLab l ({x, y} : Finset (Fin M)) = edgeLab l (edgePos x.val y.val) := by
  have h : ({x, y} : Finset (Fin M)).Nonempty := ⟨x, by simp⟩
  have hcard : ({x, y} : Finset (Fin M)).card = 2 := Finset.card_pair (ne_of_lt hxy)
  rw [roseLab, dif_pos h, if_neg (by rw [hcard]; omega), pair_min' hxy, pair_max' hxy]

end Labels

/-! ### The attaching map -/

section Att

variable {α : Type u}

/-- The nerve of the concrete block: the cycle with `2·|u|` vertices. -/
def cycA (l : List (α × Bool)) (hl : 2 ≤ l.length) : CommRel (Fin (2 * l.length)) :=
  cycRel _ (by omega)

theorem cycA_rel (l : List (α × Bool)) (hl : 2 ≤ l.length) {x y : Fin (2 * l.length)}
    (h : (cycA l hl).rel x y) : cycAdj _ x y := h

/-- **The key monotonicity step**: an endpoint of an edge of the cycle carries a label below the
label of the edge. -/
theorem roseLab_vertex_le_edge (l : List (α × Bool)) (hl : 2 ≤ l.length)
    {x y v : Fin (2 * l.length)} (hlt : x < y)
    (hadj : cycAdj (2 * l.length) x y) (hv : v = x ∨ v = y) :
    vertLab l v.val ≤ edgeLab l (edgePos x.val y.val) := by
  have hxlt := x.isLt
  have hylt := y.isLt
  have hxy' : x.val < y.val := hlt
  have hcase : y.val = x.val + 1 ∨ (x.val = 0 ∧ y.val + 1 = 2 * l.length) := by
    simp only [cycAdj] at hadj
    omega
  rcases hcase with h1 | ⟨h0, hM1⟩
  · have hpos : edgePos x.val y.val = x.val := by simp [edgePos, h1]
    rw [hpos]
    rcases hv with rfl | rfl
    · exact vertLab_le_edgeLab (by omega)
    · rw [h1]
      exact vertLab_succ_le_edgeLab (by omega)
  · have hpos : edgePos x.val y.val = y.val := by
      have hne : y.val ≠ x.val + 1 := by omega
      simp [edgePos, hne]
    rw [hpos]
    rcases hv with rfl | rfl
    · rw [vertLab_of_even (by omega)]
      exact base_le_edgeLab (by omega)
    · exact vertLab_le_edgeLab (by omega)

/-- The labelling is monotone on the simplices of the cycle. -/
theorem roseLab_monotone (l : List (α × Bool)) (hl : 2 ≤ l.length) : Monotone (fun σ : NeSpx (cycA l hl) => roseLab l σ.1) := by
  rintro ⟨σ, hσne, hσs⟩ ⟨τ, hτne, hτs⟩ (hsub : σ ⊆ τ)
  have hM : 4 ≤ 2 * l.length := by omega
  have hσ2 : σ.card ≤ 2 := card_le_two_of_isSimplex _ hσs
  have hτ2 : τ.card ≤ 2 := card_le_two_of_isSimplex _ hτs
  have hσ1 : 1 ≤ σ.card := Finset.card_pos.2 hσne
  have hcards : σ.card ≤ τ.card := Finset.card_le_card hsub
  by_cases heq : τ.card ≤ σ.card
  · have : σ = τ := Finset.eq_of_subset_of_card_le hsub heq
    subst this
    exact le_refl _
  -- the remaining case: a vertex inside an edge
  have hσc : σ.card = 1 := by omega
  have hτc : τ.card = 2 := by omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.1 hσc
  obtain ⟨x, y, hxy, hτ⟩ := Finset.card_eq_two.1 hτc
  -- normalise so that `x < y`
  have hmem : v ∈ τ := hsub (hv ▸ Finset.mem_singleton_self v)
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · subst hτ
    have hadj : cycAdj (2 * l.length) x y := hτs x (by simp) y (by simp) hxy
    show roseLab l σ ≤ roseLab l {x, y}
    rw [hv, roseLab_singleton, roseLab_pair l hlt]
    exact roseLab_vertex_le_edge l hl hlt hadj (by simpa using hmem)
  · rw [Finset.pair_comm] at hτ
    subst hτ
    have hadj : cycAdj (2 * l.length) y x := hτs y (by simp) x (by simp) (Ne.symm hxy)
    show roseLab l σ ≤ roseLab l {y, x}
    rw [hv, roseLab_singleton, roseLab_pair l hlt]
    exact roseLab_vertex_le_edge l hl hlt hadj (by
      have := hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      tauto)

end Att

end Davis
end FiniteChains
