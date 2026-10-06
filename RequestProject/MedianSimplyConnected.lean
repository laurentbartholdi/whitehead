module

public import RequestProject.MedianSquareComplexWalls
public import RequestProject.SquareComplexWalkHomotopy

@[expose] public section

/-!
# The square complex of a median graph is simply connected, and its links are flag

The remaining cited geometric input of the cube-complex branch is Gromov's criterion,

> a simply connected cube complex with flag links has median one–skeleton.

This file proves the **converse** implication, which is the elementary one, and proves it from
scratch: the square complex of a median graph (one-skeleton the graph, two-cells the
four-cycles) is simply connected, has no triangles, and satisfies the link (flag) condition.
Hence the hypotheses of the criterion are not only sufficient but also necessary, and the
combinatorial formulation used in this project is the right one.

The main results are

* `FiniteChains.MedianGraph.dist_ne_of_dist_one` — a median graph is bipartite: adjacent
  vertices have different distances to any vertex;
* `FiniteChains.MedianGraph.quadrangle` — the quadrangle condition: two distinct neighbours
  `u, v` of a vertex `q`, both one step closer to `x` than `q` is, have a common neighbour
  `med u v x ≠ q` one further step closer to `x`;
* `FiniteChains.MedianSimpleGraph.toSquareComplex_simplyConnected` — **every closed walk of a
  median graph contracts through four-cycles**: the square complex is simply connected.  The
  proof is the combinatorial Cartan–Hadamard argument: in a closed walk based at `x` which is
  not the constant walk there is a vertex `q` strictly higher than both its neighbours in the
  walk (`FiniteChains.exists_peak`), and the quadrangle condition either cancels a backtrack or
  pushes the walk across a square onto a strictly lower walk;
* `FiniteChains.MedianSimpleGraph.toSquareComplex_no_triangle` — the one-skeleton has no
  triangles;
* `FiniteChains.MedianGraph.cube_condition` — the link condition: three distinct neighbours of
  a vertex that pairwise span squares span a three-dimensional cube.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

universe u

/-! ### A peak of a list of values -/

/-- **Existence of a peak.**  Along a list whose consecutive values of `f` differ, which starts
by going up and whose last value is below the second one, there is an entry strictly higher
than both of its neighbours. -/
theorem exists_peak {Vx : Type u} (f : Vx → ℕ) :
    ∀ (t : List Vx) (a p : Vx), List.IsChain (fun u v => f u ≠ f v) (a :: p :: t) →
      f a < f p → (∀ z, (a :: p :: t).getLast? = some z → f z < f p) →
      ∃ (pre : List Vx) (u q v : Vx) (suf : List Vx),
        a :: p :: t = pre ++ u :: q :: v :: suf ∧ f u < f q ∧ f v < f q := by
  intro t
  induction t with
  | nil =>
      intro a p _ _ hlast
      exact absurd (hlast p (by simp)) (lt_irrefl _)
  | cons b t ih =>
      intro a p hchain hap hlast
      rcases lt_or_ge (f b) (f p) with hb | hb
      · exact ⟨[], a, p, b, t, rfl, hap, hb⟩
      · have hne : f p ≠ f b := by
          rw [List.isChain_cons_cons] at hchain
          rw [List.isChain_cons_cons] at hchain
          exact hchain.2.1
        have hpb : f p < f b := lt_of_le_of_ne hb hne
        have hchain' : List.IsChain (fun u v => f u ≠ f v) (p :: b :: t) := by
          rw [List.isChain_cons_cons] at hchain
          exact hchain.2
        have hlast' : ∀ z, (p :: b :: t).getLast? = some z → f z < f b := by
          intro z hz
          have : (a :: p :: b :: t).getLast? = some z := by
            simpa using hz
          exact lt_trans (hlast z this) hpb
        obtain ⟨pre, u, q, v, suf, heq, h1, h2⟩ := ih p b hchain' hpb hlast'
        exact ⟨a :: pre, u, q, v, suf, by rw [List.cons_append, ← heq], h1, h2⟩

namespace MedianGraph

variable {Vx : Type u} {G : MedianGraph Vx}

/-- **Median graphs are bipartite**: the two endpoints of an edge are at different distances
from any vertex. -/
theorem dist_ne_of_dist_one {x p q : Vx} (h : G.dist p q = 1) :
    G.dist x p ≠ G.dist x q := by
  intro hxy
  have hab := G.med_ab p q x
  have hbc := G.med_bc p q x
  have hac := G.med_ac p q x
  rw [h] at hab
  have hpx : G.dist p x = G.dist x p := G.dist_comm p x
  have hqx : G.dist q x = G.dist x q := G.dist_comm q x
  rcases Nat.eq_zero_or_pos (G.dist p (G.med p q x)) with h0 | h0
  · have hm : p = G.med p q x := G.eq_of_dist_eq_zero h0
    rw [← hm] at hbc
    rw [G.dist_comm q p, h] at hbc
    omega
  · have h1 : G.dist (G.med p q x) q = 0 := by omega
    have hm : G.med p q x = q := G.eq_of_dist_eq_zero h1
    rw [hm, h] at hac
    omega

/-- **The quadrangle condition.**  If `u ≠ v` are both adjacent to `q` and both one step closer
to `x` than `q`, then `m = med u v x` is a common neighbour of `u` and `v`, different from `q`,
and one further step closer to `x`. -/
theorem quadrangle {x u q v : Vx} (hu : G.dist u q = 1) (hv : G.dist q v = 1) (huv : u ≠ v)
    (hlu : G.dist x u + 1 = G.dist x q) (hlv : G.dist x v + 1 = G.dist x q) :
    G.dist u (G.med u v x) = 1 ∧ G.dist v (G.med u v x) = 1 ∧
      G.dist x (G.med u v x) + 1 = G.dist x u ∧ G.med u v x ≠ q := by
  have huv2 : G.dist u v = 2 := by
    have hle : G.dist u v ≤ 2 := by
      have := G.dist_triangle u q v
      omega
    have hne0 : G.dist u v ≠ 0 := fun h => huv (G.eq_of_dist_eq_zero h)
    have hne1 : G.dist u v ≠ 1 := by
      intro h
      exact dist_ne_of_dist_one (x := x) h (by omega)
    omega
  have hab := G.med_ab u v x
  have hbc := G.med_bc u v x
  have hac := G.med_ac u v x
  rw [huv2] at hab
  have hux : G.dist u x = G.dist x u := G.dist_comm u x
  have hvx : G.dist v x = G.dist x v := G.dist_comm v x
  have hmx : G.dist (G.med u v x) x = G.dist x (G.med u v x) := G.dist_comm _ x
  have hvm : G.dist v (G.med u v x) = G.dist (G.med u v x) v := G.dist_comm _ _
  refine ⟨by omega, by omega, by omega, ?_⟩
  intro h
  rw [h] at hac
  rw [G.dist_comm q x] at hac
  omega

end MedianGraph

namespace MedianSimpleGraph

variable {Vx : Type u} (M : MedianSimpleGraph Vx)

open SquareComplex

/-- Elementary moves may be performed after any initial segment. -/
theorem move_append {S : SquareComplex Vx} (pre : List Vx) {l l' : List Vx}
    (h : S.Move l l') : S.Move (pre ++ l) (pre ++ l') := by
  induction pre with
  | nil => simpa using h
  | cons a pre ih => simpa using Move.cons a ih

/-! ### The median conditions at the level of the graph -/

/-- Adjacent vertices are at different distances from any vertex (median graphs are
bipartite). -/
theorem dist_ne_of_adj {x p q : Vx} (h : M.G.Adj p q) : M.G.dist x p ≠ M.G.dist x q :=
  MedianGraph.dist_ne_of_dist_one (G := M.toMedianGraph) (x := x) (M.dist_eq_one_iff_adj.2 h)

/-- Distance zero means equality. -/
theorem eq_of_gdist_eq_zero {x y : Vx} (h : M.G.dist x y = 0) : x = y :=
  (M.toMedianGraph).eq_of_dist_eq_zero h

/-- The triangle inequality for the graph distance. -/
theorem gdist_triangle (x y z : Vx) : M.G.dist x z ≤ M.G.dist x y + M.G.dist y z :=
  (M.toMedianGraph).dist_triangle x y z

/-- **The quadrangle condition**, at the level of the graph: two distinct neighbours `u, v` of
`q`, both one step closer to `x`, have a common neighbour `med u v x ≠ q` one further step
closer to `x`. -/
theorem quadrangle_graph {x u q v : Vx} (huq : M.G.Adj u q) (hqv : M.G.Adj q v) (huv : u ≠ v)
    (hlu : M.G.dist x u + 1 = M.G.dist x q) (hlv : M.G.dist x v + 1 = M.G.dist x q) :
    M.G.Adj u (M.med u v x) ∧ M.G.Adj v (M.med u v x) ∧
      M.G.dist x (M.med u v x) + 1 = M.G.dist x u ∧ M.med u v x ≠ q := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    MedianGraph.quadrangle (G := M.toMedianGraph) (x := x)
      (M.dist_eq_one_iff_adj.2 huq) (M.dist_eq_one_iff_adj.2 hqv) huv hlu hlv
  exact ⟨M.dist_eq_one_iff_adj.1 h1, M.dist_eq_one_iff_adj.1 h2, h3, h4⟩

/-! ### Simple connectivity -/

/-- A closed walk all of whose vertices are the base point is the constant walk. -/
theorem closed_walk_eq_singleton {x : Vx} {l : List Vx}
    (hl : (M.toSquareComplex).IsClosedWalk x l) (h0 : ∀ y ∈ l, M.G.dist x y = 0) : l = [x] := by
  obtain ⟨hw, hh, _⟩ := hl
  rcases l with _ | ⟨a, t⟩
  · simp at hh
  · have hax : a = x := by simpa using hh
    subst hax
    rcases t with _ | ⟨b, t⟩
    · rfl
    · exfalso
      have hadj : M.G.Adj a b := (List.isChain_cons_cons.1 hw).1
      have hb : M.G.dist a b = 0 := h0 b (by simp)
      have hba : b = a := (M.eq_of_gdist_eq_zero hb).symm
      subst hba
      exact M.G.irrefl hadj

/-- The auxiliary induction behind simple connectivity: a closed walk whose vertices have total
distance at most `n` to the base point contracts to the base point. -/
theorem null_homotopic_aux (x : Vx) : ∀ (n : ℕ) (l : List Vx),
    (l.map (fun v => M.G.dist x v)).sum ≤ n →
    (M.toSquareComplex).IsClosedWalk x l → (M.toSquareComplex).WalkHomotopic l [x] := by
  intro n
  induction n with
  | zero =>
      intro l hsum hl
      have h0 : ∀ y ∈ l, M.G.dist x y = 0 := by
        intro y hy
        have hle : M.G.dist x y ≤ (l.map (fun v => M.G.dist x v)).sum :=
          List.single_le_sum (by intro z _; exact Nat.zero_le z) _ (List.mem_map_of_mem hy)
        omega
      rw [closed_walk_eq_singleton M hl h0]
      exact SquareComplex.WalkHomotopic.refl _
  | succ n ih =>
      intro l hsum hl
      classical
      by_cases hsingle : l = [x]
      · rw [hsingle]
        exact SquareComplex.WalkHomotopic.refl _
      obtain ⟨hw, hh, hlast⟩ := hl
      rcases l with _ | ⟨a, t⟩
      · simp at hh
      have hax : a = x := by simpa using hh
      subst hax
      rcases t with _ | ⟨b, t⟩
      · exact absurd rfl hsingle
      have hadj0 : M.G.Adj a b := (List.isChain_cons_cons.1 hw).1
      have hchain : List.IsChain (fun u v => M.G.dist a u ≠ M.G.dist a v) (a :: b :: t) :=
        hw.imp fun _ _ hpq => M.dist_ne_of_adj hpq
      have hfa : M.G.dist a a = 0 := SimpleGraph.dist_self
      have hab : M.G.dist a a < M.G.dist a b := by
        have := M.dist_ne_of_adj (x := a) hadj0
        omega
      have hlast' : ∀ z, (a :: b :: t).getLast? = some z → M.G.dist a z < M.G.dist a b := by
        intro z hz
        have hz' : z = a := by
          rw [hlast] at hz
          simpa using hz.symm
        subst hz'
        omega
      obtain ⟨pre, u, q, v, suf, heq, hu, hv⟩ :=
        exists_peak (fun y => M.G.dist a y) t a b hchain hab hlast'
      rw [heq] at hw hlast hsum ⊢
      have hchain2 : List.IsChain M.G.Adj (u :: q :: v :: suf) :=
        (List.isChain_append.1 hw).2.1
      have huq : M.G.Adj u q := (List.isChain_cons_cons.1 hchain2).1
      have hqv : M.G.Adj q v := (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hchain2).2).1
      have hhh : (pre ++ u :: q :: v :: suf).head? = some a := by rw [← heq]; exact hh
      have hfu : M.G.dist a u + 1 = M.G.dist a q := by
        have h1 : M.G.dist a q ≤ M.G.dist a u + M.G.dist u q := M.gdist_triangle a u q
        have h2 : M.G.dist u q = 1 := M.dist_eq_one_iff_adj.2 huq
        omega
      have hfv : M.G.dist a v + 1 = M.G.dist a q := by
        have h1 : M.G.dist a q ≤ M.G.dist a v + M.G.dist v q := M.gdist_triangle a v q
        have h2 : M.G.dist v q = 1 := M.dist_eq_one_iff_adj.2 (M.G.symm.symm _ _ hqv)
        omega
      by_cases huv : u = v
      · -- the peak is a backtrack
        subst huv
        have hmove : (M.toSquareComplex).Move (pre ++ u :: q :: u :: suf) (pre ++ u :: suf) :=
          move_append pre (SquareComplex.Move.backtrack u q suf)
        refine SquareComplex.WalkHomotopic.head_walkMove (Or.inl ⟨hmove, hw⟩) (ih _ ?_ ?_)
        · simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons] at hsum ⊢
          omega
        · exact SquareComplex.IsClosedWalk.of_move hmove ⟨hw, hhh, hlast⟩
      · -- push the peak across a square
        obtain ⟨hmu, hmv, hmx, hmq⟩ := M.quadrangle_graph huq hqv huv hfu hfv
        have hsq : (M.toSquareComplex).sq u q v (M.med u v a) :=
          ⟨huq, hqv, hmv, M.G.symm.symm _ _ hmu, huv, fun h => hmq h.symm⟩
        have hmove : (M.toSquareComplex).Move (pre ++ u :: q :: v :: suf)
            (pre ++ u :: M.med u v a :: v :: suf) :=
          move_append pre (SquareComplex.Move.square hsq suf)
        refine SquareComplex.WalkHomotopic.head_walkMove (Or.inl ⟨hmove, hw⟩) (ih _ ?_ ?_)
        · simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons] at hsum ⊢
          omega
        · exact SquareComplex.IsClosedWalk.of_move hmove ⟨hw, hhh, hlast⟩

/-- **The square complex of a median graph is simply connected**: every closed walk contracts
to its base point through backtracks and four-cycles.  This is the converse half of the
criterion "a simply connected cube complex with flag links has median one-skeleton". -/
theorem toSquareComplex_simplyConnectedW :
    SquareComplex.SimplyConnectedW M.toSquareComplex := fun x l hl =>
  null_homotopic_aux M x _ l le_rfl hl

/-- The same statement for the coarser homotopy relation of
`RequestProject/SquareComplexWalls.lean`. -/
theorem toSquareComplex_simplyConnected :
    SquareComplex.SimplyConnected M.toSquareComplex :=
  (toSquareComplex_simplyConnectedW M).simplyConnected

/-- The one-skeleton of a median graph has no triangles. -/
theorem no_triangle {a b c : Vx} (hab : M.G.Adj a b) (hbc : M.G.Adj b c)
    (hca : M.G.Adj c a) : False := by
  have h1 : M.G.dist a b = 1 := M.dist_eq_one_iff_adj.2 hab
  have h2 : M.G.dist a c = 1 := M.dist_eq_one_iff_adj.2 (M.G.symm.symm _ _ hca)
  exact M.dist_ne_of_adj (x := a) hbc (by rw [h1, h2])

/-! ### The link (flag) condition -/

/-- Two distinct vertices with a common neighbour are at distance two. -/
theorem gdist_two_of_common_neighbour {a b z : Vx} (ha : M.G.Adj a z) (hb : M.G.Adj b z)
    (hab : a ≠ b) : M.G.dist a b = 2 :=
  MedianGraph.dist_eq_two_of_common_neighbour (G := M.toMedianGraph)
    (M.dist_eq_one_iff_adj.2 ha) (M.dist_eq_one_iff_adj.2 hb) hab

/-- **A median graph contains no `K₂,₃`**: two vertices at distance two have at most two
common neighbours. -/
theorem no_K23 {x y u v t : Vx} (hxy : M.G.dist x y = 2) (hux : M.G.Adj u x) (huy : M.G.Adj u y)
    (hvx : M.G.Adj v x) (hvy : M.G.Adj v y) (htx : M.G.Adj t x) (hty : M.G.Adj t y)
    (huv : u ≠ v) (hut : u ≠ t) (hvt : v ≠ t) : False :=
  MedianGraph.not_three_common_neighbours (G := M.toMedianGraph) hxy
    (M.dist_eq_one_iff_adj.2 hux) (M.dist_eq_one_iff_adj.2 huy)
    (M.dist_eq_one_iff_adj.2 hvx) (M.dist_eq_one_iff_adj.2 hvy)
    (M.dist_eq_one_iff_adj.2 htx) (M.dist_eq_one_iff_adj.2 hty) huv hut hvt

/-- **The link condition (flagness) at an arbitrary vertex.**  If three distinct neighbours
`a, b, c` of `w` pairwise span squares — `p` closes the square on `a, b`, `q` the one on
`a, c`, `r` the one on `b, c` — then the three squares close up to a three-dimensional cube:
`med p q r` is a common neighbour of `p`, `q` and `r`, at distance three from `w`. -/
theorem cube_condition {w a b c p q r : Vx}
    (hwa : M.G.Adj w a) (hwb : M.G.Adj w b) (hwc : M.G.Adj w c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpa : M.G.Adj p a) (hpb : M.G.Adj p b) (hpw : p ≠ w)
    (hqa : M.G.Adj q a) (hqc : M.G.Adj q c) (hqw : q ≠ w)
    (hrb : M.G.Adj r b) (hrc : M.G.Adj r c) (hrw : r ≠ w) :
    M.G.Adj p (M.med p q r) ∧ M.G.Adj q (M.med p q r) ∧ M.G.Adj r (M.med p q r) ∧
      M.G.dist w (M.med p q r) = 3 := by
  have hwp : M.G.dist w p = 2 := M.gdist_two_of_common_neighbour hwa hpa (Ne.symm hpw)
  have hwq : M.G.dist w q = 2 := M.gdist_two_of_common_neighbour hwa hqa (Ne.symm hqw)
  have hwr : M.G.dist w r = 2 := M.gdist_two_of_common_neighbour hwb hrb (Ne.symm hrw)
  -- the three corners are pairwise distinct
  have hpq : p ≠ q := by
    intro h
    subst h
    exact M.no_K23 (x := w) (y := p) (u := a) (v := b) (t := c) hwp
      (M.G.symm.symm _ _ hwa) (M.G.symm.symm _ _ hpa) (M.G.symm.symm _ _ hwb) (M.G.symm.symm _ _ hpb)
      (M.G.symm.symm _ _ hwc) (M.G.symm.symm _ _ hqc) hab hac hbc
  have hpr : p ≠ r := by
    intro h
    subst h
    exact M.no_K23 (x := w) (y := p) (u := a) (v := b) (t := c) hwp
      (M.G.symm.symm _ _ hwa) (M.G.symm.symm _ _ hpa) (M.G.symm.symm _ _ hwb) (M.G.symm.symm _ _ hpb)
      (M.G.symm.symm _ _ hwc) (M.G.symm.symm _ _ hrc) hab hac hbc
  have hqr : q ≠ r := by
    intro h
    subst h
    exact M.no_K23 (x := w) (y := q) (u := a) (v := b) (t := c) hwq
      (M.G.symm.symm _ _ hwa) (M.G.symm.symm _ _ hqa) (M.G.symm.symm _ _ hwb) (M.G.symm.symm _ _ hrb)
      (M.G.symm.symm _ _ hwc) (M.G.symm.symm _ _ hqc) hab hac hbc
  have dpq : M.G.dist p q = 2 := M.gdist_two_of_common_neighbour hpa hqa hpq
  have dpr : M.G.dist p r = 2 := M.gdist_two_of_common_neighbour hpb hrb hpr
  have dqr : M.G.dist q r = 2 := M.gdist_two_of_common_neighbour hqc hrc hqr
  set t := M.med p q r with ht
  have e1 : M.G.dist p t + M.G.dist t q = M.G.dist p q := M.med_ab p q r
  have e2 : M.G.dist q t + M.G.dist t r = M.G.dist q r := M.med_bc p q r
  have e3 : M.G.dist p t + M.G.dist t r = M.G.dist p r := M.med_ac p q r
  have cqt : M.G.dist q t = M.G.dist t q := SimpleGraph.dist_comm
  have crt : M.G.dist r t = M.G.dist t r := SimpleGraph.dist_comm
  have d1 : M.G.dist p t = 1 := by omega
  have d2 : M.G.dist t q = 1 := by omega
  have d3 : M.G.dist t r = 1 := by omega
  have hpt : M.G.Adj p t := M.dist_eq_one_iff_adj.1 d1
  have hqt : M.G.Adj q t := M.dist_eq_one_iff_adj.1 (show M.G.dist q t = 1 by omega)
  have hrt : M.G.Adj r t := M.dist_eq_one_iff_adj.1 (show M.G.dist r t = 1 by omega)
  refine ⟨hpt, hqt, hrt, ?_⟩
  -- the opposite corner of the cube is at distance three from `w`
  have hta : t ≠ a := by
    intro h
    have hra : M.G.Adj r a := by rw [← h]; exact hrt
    exact M.no_K23 (x := w) (y := r) (u := a) (v := b) (t := c) hwr
      (M.G.symm.symm _ _ hwa) (M.G.symm.symm _ _ hra) (M.G.symm.symm _ _ hwb) (M.G.symm.symm _ _ hrb)
      (M.G.symm.symm _ _ hwc) (M.G.symm.symm _ _ hrc) hab hac hbc
  have htb : t ≠ b := by
    intro h
    have hqb : M.G.Adj q b := by rw [← h]; exact hqt
    exact M.no_K23 (x := w) (y := q) (u := a) (v := b) (t := c) hwq
      (M.G.symm.symm _ _ hwa) (M.G.symm.symm _ _ hqa) (M.G.symm.symm _ _ hwb) (M.G.symm.symm _ _ hqb)
      (M.G.symm.symm _ _ hwc) (M.G.symm.symm _ _ hqc) hab hac hbc
  have hne1 : M.G.dist w t ≠ 1 := by
    intro h
    have hwt : M.G.Adj w t := M.dist_eq_one_iff_adj.1 h
    exact M.no_K23 (x := w) (y := p) (u := a) (v := b) (t := t) hwp
      (M.G.symm.symm _ _ hwa) (M.G.symm.symm _ _ hpa) (M.G.symm.symm _ _ hwb) (M.G.symm.symm _ _ hpb)
      (M.G.symm.symm _ _ hwt) (M.G.symm.symm _ _ hpt) hab (Ne.symm hta) (Ne.symm htb)
  have hne2 : M.G.dist w t ≠ 2 := by
    intro h
    exact M.dist_ne_of_adj (x := w) hpt (by rw [hwp, h])
  have hne0 : M.G.dist w t ≠ 0 := by
    intro h
    have hwt : w = t := M.eq_of_gdist_eq_zero h
    have h1 : M.G.dist p w = 1 := by rw [hwt]; exact d1
    have h2 : M.G.dist w p = M.G.dist p w := SimpleGraph.dist_comm
    omega
  have hle : M.G.dist w t ≤ 3 := by
    have := M.gdist_triangle w p t
    omega
  omega

end MedianSimpleGraph

end FiniteChains
