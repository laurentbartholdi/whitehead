import RequestProject.MedianGraphMetric

/-!
# The cells of the descending-cube structure are the cubes of the median graph

`RequestProject/CubeMedianGraph.lean` builds, out of a median graph `G` of dimension at most
three, a `FiniteChains.DescCubeStr` whose two- and three-cells are recorded as a top vertex
together with two (resp. three) descending neighbours listed in increasing order.  For the
step "identify the cellular chains of the space with the chains of the model" one needs to
know that these bookkeeping data really are the squares and the three-dimensional cubes of the
graph.  This file proves exactly that, intrinsically in the graph:

* `FiniteChains.MedianGraph.ht_adj` — the endpoints of an edge differ in height by one, so
  every edge is descending from exactly one of its endpoints;
* `FiniteChains.MedianGraph.square_of_dn` — the two descending edges of a two-cell close up to
  a genuine four-cycle `w — a — m — b — w` of the graph, with the two diagonals at distance
  two and the fourth vertex two levels below `w`;
* `FiniteChains.MedianGraph.eq_med_of_common_neighbour` — conversely, a four-cycle through the
  two descending edges is unique: any common neighbour of `a` and `b` other than `w` is the
  fourth vertex of the cell.  Hence two-cells at `w` correspond bijectively to four-cycles of
  the graph having `w` as their unique top vertex;
* `FiniteChains.MedianGraph.cube_ht`, `FiniteChains.MedianGraph.cube_vertices_distinct`,
  `FiniteChains.MedianGraph.cube_edges` — the eight vertices attached to a three-cell are
  pairwise distinct, lie on the four consecutive levels `ht w`, `ht w - 1`, `ht w - 2`,
  `ht w - 3`, and carry the twelve edges of a three-dimensional cube.

Together with `RequestProject/MedianGraphMetric.lean` (the metric of a median graph is the
edge metric of a connected graph) this says: the chain complex used in
`FiniteChains.MedianGraph.ker_d₂_eq_range_d₃` is the cellular chain complex, in degrees one to
three, of the cube complex whose one-skeleton is the graph, its squares the four-cycles and
its three-cells the graph three-cubes.
-/

namespace FiniteChains

namespace MedianGraph

universe u

variable {Vx : Type u} {G : MedianGraph Vx}

/-- **Edges change the height by exactly one.**  Hence each edge descends from exactly one of
its endpoints, and the graph carries no edge inside a level. -/
theorem ht_adj {a w : Vx} (h : G.dist a w = 1) :
    G.ht a + 1 = G.ht w ∨ G.ht w + 1 = G.ht a := by
  have e1 : G.dist a (G.med a w G.base) + G.dist (G.med a w G.base) w = G.dist a w :=
    G.med_ab a w G.base
  have e2 : G.dist w (G.med a w G.base) + G.dist (G.med a w G.base) G.base = G.dist w G.base :=
    G.med_bc a w G.base
  have e3 : G.dist a (G.med a w G.base) + G.dist (G.med a w G.base) G.base = G.dist a G.base :=
    G.med_ac a w G.base
  have hta : G.dist a G.base = G.ht a := (ht_eq a).symm
  have htw : G.dist w G.base = G.ht w := (ht_eq w).symm
  rw [h] at e1
  rcases Nat.eq_zero_or_pos (G.dist a (G.med a w G.base)) with h0 | h0
  · -- the median is `a`
    have hza : a = G.med a w G.base := G.eq_of_dist_eq_zero h0
    rw [← hza] at e2
    rw [G.dist_comm w a, h] at e2
    left
    omega
  · -- the median is `w`
    have hzw : G.dist (G.med a w G.base) w = 0 := by omega
    have hwz : G.med a w G.base = w := G.eq_of_dist_eq_zero hzw
    rw [hwz, h] at e3
    right
    omega

/-- **Two descending edges close up to a four-cycle.**  For two distinct descending neighbours
`a`, `b` of `w`, the fourth vertex `m = med a b base` of the two-cell is adjacent to `a` and to
`b`, lies two levels below `w`, and the two diagonals `a, b` and `m, w` are at distance two: the
four vertices span a square of the graph. -/
theorem square_of_dn {w a b : Vx} (ha : a ∈ G.dnM w) (hb : b ∈ G.dnM w) (hab : a ≠ b) :
    G.dist a w = 1 ∧ G.dist b w = 1 ∧
      G.dist (G.med a b G.base) a = 1 ∧ G.dist (G.med a b G.base) b = 1 ∧
      G.dist a b = 2 ∧ G.dist (G.med a b G.base) w = 2 ∧
      G.ht (G.med a b G.base) + 2 = G.ht w := by
  obtain ⟨h1, h2, h3⟩ := med_square ha hb hab
  refine ⟨ha.1, hb.1, h1, h2, dist_dn_eq_two ha hb hab, dist_med_top ha hb hab, ?_⟩
  have := ha.2
  omega

/-- The fourth vertex of a two-cell is distinct from its top vertex. -/
theorem med_ne_top {w a b : Vx} (ha : a ∈ G.dnM w) (hb : b ∈ G.dnM w) (hab : a ≠ b) :
    G.med a b G.base ≠ w := by
  intro h
  have h2 := dist_med_top ha hb hab
  rw [h, G.dist_self] at h2
  omega

/-- **The four-cycle through two descending edges is unique.**  Any common neighbour of two
distinct descending neighbours `a`, `b` of `w`, other than `w` itself, is the fourth vertex of
the two-cell they span.  Hence the two-cells with top vertex `w` are exactly the four-cycles of
the graph in which the two neighbours of `w` are descending. -/
theorem eq_med_of_common_neighbour {w a b c : Vx} (ha : a ∈ G.dnM w) (hb : b ∈ G.dnM w)
    (hab : a ≠ b) (hca : G.dist c a = 1) (hcb : G.dist c b = 1) (hcw : c ≠ w) :
    c = G.med a b G.base := by
  by_contra hne
  obtain ⟨hma, hmb, hmh⟩ := med_square ha hb hab
  have hmw : G.med a b G.base ≠ w := med_ne_top ha hb hab
  refine not_three_common_neighbours (x := a) (y := b) (u := w) (v := c)
    (t := G.med a b G.base) (dist_dn_eq_two ha hb hab)
    (by rw [G.dist_comm]; exact ha.1) (by rw [G.dist_comm]; exact hb.1) hca hcb hma hmb
    (Ne.symm hcw) (Ne.symm hmw) hne

/-- The three squares of a three-cell meet in a common bottom vertex, which is the vertex
opposite to the top vertex of the cube. -/
theorem cube_bot_eq {w a b c : Vx} (ha : a ∈ G.dnM w) (hb : b ∈ G.dnM w) (hc : c ∈ G.dnM w)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    G.med (G.med a b G.base) (G.med a c G.base) G.base
      = G.med (G.med a b G.base) (G.med b c G.base) G.base ∧
    G.med (G.med a b G.base) (G.med a c G.base) G.base
      = G.med (G.med a c G.base) (G.med b c G.base) G.base :=
  med_bottom ha hb hc hab hac hbc

/-- The three second-level vertices of a three-cell are pairwise distinct. -/
theorem cube_mid_distinct {w a b c : Vx} (ha : a ∈ G.dnM w) (hb : b ∈ G.dnM w) (hc : c ∈ G.dnM w)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    G.med a b G.base ≠ G.med a c G.base ∧ G.med a b G.base ≠ G.med b c G.base ∧
      G.med a c G.base ≠ G.med b c G.base := by
  refine ⟨med_ne_med ha hb hc hab hac hbc, ?_, ?_⟩
  · have h := med_ne_med hb ha hc (Ne.symm hab) hbc hac
    rwa [med_swap b a G.base] at h
  · have h := med_ne_med hc ha hb (Ne.symm hac) (Ne.symm hbc) hab
    rwa [med_swap c a G.base, med_swap c b G.base] at h

/-- **The eight vertices of a three-cell lie on four consecutive levels**: the top vertex `w`,
the three descending neighbours one level below, the three square vertices two levels below,
and the bottom vertex three levels below. -/
theorem cube_ht {w a b c : Vx} (ha : a ∈ G.dnM w) (hb : b ∈ G.dnM w) (hc : c ∈ G.dnM w)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    G.ht a + 1 = G.ht w ∧ G.ht b + 1 = G.ht w ∧ G.ht c + 1 = G.ht w ∧
      G.ht (G.med a b G.base) + 2 = G.ht w ∧ G.ht (G.med a c G.base) + 2 = G.ht w ∧
      G.ht (G.med b c G.base) + 2 = G.ht w ∧
      G.ht (G.med (G.med a b G.base) (G.med a c G.base) G.base) + 3 = G.ht w := by
  obtain ⟨-, -, -, -, -, -, hab2⟩ := square_of_dn ha hb hab
  obtain ⟨-, -, -, -, -, -, hac2⟩ := square_of_dn ha hc hac
  obtain ⟨-, -, -, -, -, -, hbc2⟩ := square_of_dn hb hc hbc
  have hma : G.med a b G.base ∈ G.dnM a := med_mem_dn ha hb hab
  have hma' : G.med a c G.base ∈ G.dnM a := med_mem_dn ha hc hac
  have hne : G.med a b G.base ≠ G.med a c G.base := med_ne_med ha hb hc hab hac hbc
  obtain ⟨-, -, hbot⟩ := med_square hma hma' hne
  exact ⟨ha.2, hb.2, hc.2, hab2, hac2, hbc2, by omega⟩

/-- **The twelve edges of a three-cell.**  The eight vertices attached to a three-cell carry
all twelve edges of a three-dimensional cube. -/
theorem cube_edges {w a b c : Vx} (ha : a ∈ G.dnM w) (hb : b ∈ G.dnM w) (hc : c ∈ G.dnM w)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    G.dist a w = 1 ∧ G.dist b w = 1 ∧ G.dist c w = 1 ∧
      G.dist (G.med a b G.base) a = 1 ∧ G.dist (G.med a b G.base) b = 1 ∧
      G.dist (G.med a c G.base) a = 1 ∧ G.dist (G.med a c G.base) c = 1 ∧
      G.dist (G.med b c G.base) b = 1 ∧ G.dist (G.med b c G.base) c = 1 ∧
      G.dist (G.med (G.med a b G.base) (G.med a c G.base) G.base) (G.med a b G.base) = 1 ∧
      G.dist (G.med (G.med a b G.base) (G.med a c G.base) G.base) (G.med a c G.base) = 1 ∧
      G.dist (G.med (G.med a b G.base) (G.med a c G.base) G.base) (G.med b c G.base) = 1 := by
  obtain ⟨h4, h5, -⟩ := med_square ha hb hab
  obtain ⟨h6, h7, -⟩ := med_square ha hc hac
  obtain ⟨h8, h9, -⟩ := med_square hb hc hbc
  have hma : G.med a b G.base ∈ G.dnM a := med_mem_dn ha hb hab
  have hma' : G.med a c G.base ∈ G.dnM a := med_mem_dn ha hc hac
  have hne : G.med a b G.base ≠ G.med a c G.base := med_ne_med ha hb hc hab hac hbc
  obtain ⟨h10, h11, -⟩ := med_square hma hma' hne
  -- the third square at the bottom vertex, using the cube identity
  have hmb : G.med a b G.base ∈ G.dnM b := by
    have := med_mem_dn hb ha (Ne.symm hab)
    rwa [med_swap b a G.base] at this
  have hmb' : G.med b c G.base ∈ G.dnM b := med_mem_dn hb hc hbc
  have hne' : G.med a b G.base ≠ G.med b c G.base := (cube_mid_distinct ha hb hc hab hac hbc).2.1
  obtain ⟨-, h12, -⟩ := med_square hmb hmb' hne'
  have hbot := (cube_bot_eq ha hb hc hab hac hbc).1
  rw [hbot]
  exact ⟨ha.1, hb.1, hc.1, h4, h5, h6, h7, h8, h9, by rw [← hbot]; exact h10,
    by rw [← hbot]; exact h11, h12⟩

/-- **The eight vertices of a three-cell are pairwise distinct.** -/
theorem cube_vertices_distinct {w a b c : Vx} (ha : a ∈ G.dnM w) (hb : b ∈ G.dnM w)
    (hc : c ∈ G.dnM w) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ([w, a, b, c, G.med a b G.base, G.med a c G.base, G.med b c G.base,
      G.med (G.med a b G.base) (G.med a c G.base) G.base] : List Vx).Nodup := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := cube_ht ha hb hc hab hac hbc
  obtain ⟨hm1, hm2, hm3⟩ := cube_mid_distinct ha hb hc hab hac hbc
  have hdiff : ∀ {x y : Vx}, G.ht x ≠ G.ht y → x ≠ y := by
    intro x y h hxy
    exact h (by rw [hxy])
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
    and_true, not_or]
  repeat' constructor
  all_goals first
    | exact not_false
    | exact hdiff (by omega)
    | exact hab | exact hac | exact hbc
    | exact hm1 | exact hm2 | exact hm3

/-! ### The cells of the chain complex -/

/-- **Each two-cell of the chain complex is a four-cycle of the graph.** -/
theorem sqC_isSquare [LinearOrder Vx] (F : (G.toDescCubeStr).SqC) :
    G.dist F.x F.top = 1 ∧ G.dist F.y F.top = 1 ∧
      G.dist (G.med F.x F.y G.base) F.x = 1 ∧ G.dist (G.med F.x F.y G.base) F.y = 1 ∧
      G.dist F.x F.y = 2 ∧ G.dist (G.med F.x F.y G.base) F.top = 2 ∧
      G.ht (G.med F.x F.y G.base) + 2 = G.ht F.top :=
  square_of_dn F.x_mem F.y_mem (ne_of_lt F.x_lt_y)

/-- **Each three-cell of the chain complex has eight distinct vertices.** -/
theorem cbC_vertices_distinct [LinearOrder Vx] (Q : (G.toDescCubeStr).CbC) :
    ([Q.top, Q.x, Q.y, Q.z, G.med Q.x Q.y G.base, G.med Q.x Q.z G.base, G.med Q.y Q.z G.base,
      G.med (G.med Q.x Q.y G.base) (G.med Q.x Q.z G.base) G.base] : List Vx).Nodup :=
  cube_vertices_distinct Q.x_mem Q.y_mem Q.z_mem (ne_of_lt Q.x_lt_y)
    (ne_of_lt (Q.x_lt_y.trans Q.y_lt_z)) (ne_of_lt Q.y_lt_z)

/-- **Each three-cell of the chain complex carries the twelve edges of a graph three-cube.** -/
theorem cbC_edges [LinearOrder Vx] (Q : (G.toDescCubeStr).CbC) :
    G.dist Q.x Q.top = 1 ∧ G.dist Q.y Q.top = 1 ∧ G.dist Q.z Q.top = 1 ∧
      G.dist (G.med Q.x Q.y G.base) Q.x = 1 ∧ G.dist (G.med Q.x Q.y G.base) Q.y = 1 ∧
      G.dist (G.med Q.x Q.z G.base) Q.x = 1 ∧ G.dist (G.med Q.x Q.z G.base) Q.z = 1 ∧
      G.dist (G.med Q.y Q.z G.base) Q.y = 1 ∧ G.dist (G.med Q.y Q.z G.base) Q.z = 1 ∧
      G.dist (G.med (G.med Q.x Q.y G.base) (G.med Q.x Q.z G.base) G.base)
        (G.med Q.x Q.y G.base) = 1 ∧
      G.dist (G.med (G.med Q.x Q.y G.base) (G.med Q.x Q.z G.base) G.base)
        (G.med Q.x Q.z G.base) = 1 ∧
      G.dist (G.med (G.med Q.x Q.y G.base) (G.med Q.x Q.z G.base) G.base)
        (G.med Q.y Q.z G.base) = 1 :=
  cube_edges Q.x_mem Q.y_mem Q.z_mem (ne_of_lt Q.x_lt_y)
    (ne_of_lt (Q.x_lt_y.trans Q.y_lt_z)) (ne_of_lt Q.y_lt_z)

end MedianGraph

end FiniteChains
