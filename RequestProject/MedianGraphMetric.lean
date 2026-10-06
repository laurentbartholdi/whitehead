module

public import RequestProject.CubeMedianGraph

@[expose] public section

/-!
# The median hypothesis as a statement about an actual graph

`RequestProject/CubeMedianGraph.lean` derives the descending-cube axioms — and therefore the
vanishing of the second homology of the cellular chain complex — from the structure
`FiniteChains.MedianGraph`, which records a metric with values in `ℕ` together with a unique
median for every triple.

That structure is deliberately weak: nothing in it says that the metric is the *edge metric*
of a graph, i.e. that the distance between two vertices is the length of a shortest path in
which every step moves along an edge.  This file closes that gap in two directions.

## 1. Genuine median graphs

`FiniteChains.MedianSimpleGraph` records the standard graph-theoretic notion:

* a `SimpleGraph` on the vertex set,
* the hypothesis that it is **connected**, so that `SimpleGraph.dist` really is the length of
  a shortest edge path,
* a base vertex,
* a median operation which is, for that graph distance, the unique vertex lying between each
  pair of the three given vertices,
* the dimension bound stated with the *adjacency relation* of the graph.

`FiniteChains.MedianSimpleGraph.toMedianGraph` shows that such a graph is a `MedianGraph` in
the earlier sense, with `dist` the graph distance.  The audit lemmas

* `FiniteChains.MedianSimpleGraph.dist_eq_one_iff_adj` — the pairs at distance one are exactly
  the edges of the graph, so the one-cells of the derived complex are the graph edges,
* `FiniteChains.MedianSimpleGraph.mem_dnM_iff` — the descending neighbours used by the
  descending-cube axioms are the neighbours of `w` one step closer to the base vertex,
* `FiniteChains.MedianSimpleGraph.exists_walk_length_eq_dist`,
  `FiniteChains.MedianSimpleGraph.exists_geodesic_through_median` — the distance and the
  betweenness relation used in the median axioms are realised by edge paths, each step of
  which changes exactly one coordinate (moves along one edge),

record that the derived combinatorial data is the data of the graph itself.  The conclusion
`FiniteChains.MedianSimpleGraph.ker_d₂_eq_range_d₃` is therefore the vanishing of the second
homology of the cube complex whose one-skeleton is the given median graph.

## 2. Why the extra hypotheses are needed

`FiniteChains.notGraphMetric` exhibits a `MedianGraph` structure whose distance function is
*not* the edge metric of any graph: on a two-element vertex set, the distance `2` between the
two vertices admits a unique median for every triple, yet no vertex is at distance one from
another, so the associated graph has no edges and is disconnected.  This is the reason the
structure `MedianSimpleGraph` carries the graph and its connectivity explicitly, rather than
only an integer-valued metric.
-/

namespace FiniteChains

universe u

open SimpleGraph

/-- A **median graph** in the graph-theoretic sense: a connected simple graph, with the
distance being the number of edges of a shortest path, in which any three vertices have a
unique median.  `dim_le` is the dimension bound (a vertex has at most three neighbours closer
to the base vertex); it is stated with the adjacency relation of the graph. -/
structure MedianSimpleGraph (Vx : Type u) where
  /-- The graph. -/
  G : SimpleGraph Vx
  /-- The graph is connected, so that `G.dist` is the length of a shortest edge path. -/
  conn : G.Connected
  /-- The base vertex. -/
  base : Vx
  /-- The median of three vertices. -/
  med : Vx → Vx → Vx → Vx
  med_ab : ∀ a b c : Vx, G.dist a (med a b c) + G.dist (med a b c) b = G.dist a b
  med_bc : ∀ a b c : Vx, G.dist b (med a b c) + G.dist (med a b c) c = G.dist b c
  med_ac : ∀ a b c : Vx, G.dist a (med a b c) + G.dist (med a b c) c = G.dist a c
  med_unique : ∀ a b c z : Vx, G.dist a z + G.dist z b = G.dist a b →
    G.dist b z + G.dist z c = G.dist b c → G.dist a z + G.dist z c = G.dist a c → z = med a b c
  /-- The complex is at most three dimensional: a vertex has at most three neighbours closer
  to the base vertex. -/
  dim_le : ∀ (w : Vx) (s : Finset Vx),
    (∀ a ∈ s, G.Adj a w ∧ G.dist base a + 1 = G.dist base w) → s.card ≤ 3

namespace MedianSimpleGraph

variable {Vx : Type u} (M : MedianSimpleGraph Vx)

/-- A median graph, viewed as a metric with a unique median: the distance is the graph
distance, and the edges are exactly the pairs at distance one
(`MedianSimpleGraph.dist_eq_one_iff_adj`). -/
noncomputable def toMedianGraph : MedianGraph Vx where
  dist := M.G.dist
  base := M.base
  dist_self := fun _ => SimpleGraph.dist_self
  eq_of_dist_eq_zero := by
    intro x y h
    rcases SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp h with h | h
    · exact h
    · exact absurd (M.conn.preconnected x y) h
  dist_comm := fun _ _ => SimpleGraph.dist_comm
  dist_triangle := fun _ _ _ => M.conn.dist_triangle
  med := M.med
  med_ab := M.med_ab
  med_bc := M.med_bc
  med_ac := M.med_ac
  med_unique := M.med_unique
  dim_le := by
    intro w s hs
    refine M.dim_le w s fun a ha => ⟨?_, (hs a ha).2⟩
    exact SimpleGraph.dist_eq_one_iff_adj.mp (hs a ha).1

@[simp] theorem toMedianGraph_dist (x y : Vx) : M.toMedianGraph.dist x y = M.G.dist x y := rfl

@[simp] theorem toMedianGraph_base : M.toMedianGraph.base = M.base := rfl

/-- **The one-cells are the edges of the graph**: the pairs of vertices at distance one for
the metric used by the descending-cube axioms are exactly the adjacent pairs. -/
theorem dist_eq_one_iff_adj {x y : Vx} : M.toMedianGraph.dist x y = 1 ↔ M.G.Adj x y :=
  SimpleGraph.dist_eq_one_iff_adj

/-- The height function of the derived structure is the graph distance to the base vertex. -/
theorem ht_eq_dist (x : Vx) : M.toMedianGraph.ht x = M.G.dist M.base x := rfl

/-- **The descending neighbours are graph neighbours**: `a` is a descending neighbour of `w`
exactly when `a` is adjacent to `w` and one edge closer to the base vertex. -/
theorem mem_dnM_iff {a w : Vx} :
    a ∈ M.toMedianGraph.dnM w ↔ M.G.Adj a w ∧ M.G.dist M.base a + 1 = M.G.dist M.base w := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨SimpleGraph.dist_eq_one_iff_adj.mp h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨SimpleGraph.dist_eq_one_iff_adj.mpr h1, h2⟩

/-- **The distance is realised by an edge path**: between any two vertices there is a walk
whose length is their distance, i.e. a path changing one coordinate (moving along one edge)
at each step. -/
theorem exists_walk_length_eq_dist (x y : Vx) :
    ∃ p : M.G.Walk x y, p.length = M.G.dist x y :=
  (M.conn.preconnected x y).exists_walk_length_eq_dist

/-- **Betweenness is betweenness along edge paths**: if `m` satisfies the metric betweenness
condition for `a` and `b` — in particular if `m` is the median of a triple containing `a` and
`b` — then there is a shortest edge path from `a` to `b` passing through `m`. -/
theorem exists_geodesic_through_median {a b m : Vx}
    (h : M.G.dist a m + M.G.dist m b = M.G.dist a b) :
    ∃ (p : M.G.Walk a m) (q : M.G.Walk m b), p.length + q.length = M.G.dist a b := by
  obtain ⟨p, hp⟩ := M.exists_walk_length_eq_dist a m
  obtain ⟨q, hq⟩ := M.exists_walk_length_eq_dist m b
  exact ⟨p, q, by rw [hp, hq, h]⟩

/-- The descending-cube data of a median graph: heights, descending neighbours and the
squares spanned by pairs of descending edges, all computed from the graph. -/
noncomputable def toDescCubeStr [LinearOrder Vx] : DescCubeStr Vx := M.toMedianGraph.toDescCubeStr

/-- **Every two-cycle of the cellular chain complex of a three-dimensional median graph
bounds.** -/
theorem exists_d₃_eq [LinearOrder Vx] (z : (M.toDescCubeStr).SqC →₀ ℤ)
    (hz : (M.toDescCubeStr).d₂ z = 0) :
    ∃ c : (M.toDescCubeStr).CbC →₀ ℤ, (M.toDescCubeStr).d₃ c = z :=
  M.toMedianGraph.exists_d₃_eq z hz

/-- The kernel–image form: `ker d₂ = im d₃` for the cellular chains of the cube complex
whose one-skeleton is the given median graph. -/
theorem ker_d₂_eq_range_d₃ [LinearOrder Vx] :
    LinearMap.ker (M.toDescCubeStr).d₂ = LinearMap.range (M.toDescCubeStr).d₃ :=
  M.toMedianGraph.ker_d₂_eq_range_d₃

end MedianSimpleGraph

/-- **An integer metric with unique medians need not be a graph metric.**  On a two-element
vertex set, the metric taking the value `2` on distinct vertices satisfies every axiom of
`FiniteChains.MedianGraph` (the median of a triple is its majority vote), yet no two vertices
are at distance one: the associated graph has no edges at all, so the metric is not the edge
metric of a connected graph.  This is why `FiniteChains.MedianSimpleGraph` carries the graph
and its connectivity as data. -/
def notGraphMetric : MedianGraph Bool where
  dist := fun x y => if x = y then 0 else 2
  base := false
  dist_self := by decide
  eq_of_dist_eq_zero := by decide
  dist_comm := by decide
  dist_triangle := by decide
  med := fun a b c => if a = b then a else c
  med_ab := by decide
  med_bc := by decide
  med_ac := by decide
  med_unique := by decide
  dim_le := by decide

/-- In the metric of `FiniteChains.notGraphMetric` no two vertices are at distance one, so the
"edges" of the associated combinatorial complex are absent. -/
theorem notGraphMetric_no_edges (x y : Bool) : notGraphMetric.dist x y ≠ 1 := by
  revert x y; decide

end FiniteChains
