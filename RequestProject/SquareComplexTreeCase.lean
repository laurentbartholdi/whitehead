import RequestProject.TreeMedian

/-!
# Gromov's criterion in dimension one

The geometric input still quoted from the literature in the cube-complex branch is

> a simply connected cube complex with flag links has median one-skeleton.

This file proves it in dimension one, that is for a square complex with **no two-cells**: there
the link condition is vacuous, and the statement becomes "a connected simply connected graph is
a tree, and trees are median".  Both halves are proved:

* `FiniteChains.SquareComplex.toSimpleGraph` — the one-skeleton of a square complex as a simple
  graph, and `FiniteChains.SquareComplex.crossings_support` — the crossing number of a wall
  label along a walk counts, modulo two, how often the walk uses the labelled edge;
* `FiniteChains.SquareComplex.isAcyclic_of_simplyConnected` — a simply connected square complex
  without two-cells has an acyclic one-skeleton.  The proof needs no new geometry: the
  characteristic function of a single edge is a wall label (the square condition is vacuous),
  so by `FiniteChains.SquareComplex.crossings_eq_zero_of_closed` every closed walk uses that
  edge an even number of times, while a cycle uses each of its edges exactly once;
* `FiniteChains.SquareComplex.isTree_of_simplyConnected` and
  `FiniteChains.SquareComplex.medianSimpleGraph_of_simplyConnected` — hence the one-skeleton is
  a tree and, by `FiniteChains.Tree.toMedianSimpleGraph`, a median graph.  This is the
  one-dimensional case of the criterion, proved unconditionally.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

namespace SquareComplex

universe u

variable {Vx : Type u} [DecidableEq Vx] {S : SquareComplex Vx}

/-- The one-skeleton of a square complex, as a simple graph. -/
def toSimpleGraph (S : SquareComplex Vx) : SimpleGraph Vx where
  Adj := S.adj
  symm := ⟨fun _ _ h => S.adj_symm h⟩
  loopless := ⟨S.adj_irrefl⟩

omit [DecidableEq Vx] in
@[simp] theorem toSimpleGraph_adj (a b : Vx) : (toSimpleGraph S).Adj a b ↔ S.adj a b := Iff.rfl

/-- The characteristic function of a single edge. -/
def edgeLabel (e : Sym2 Vx) : Vx → Vx → ZMod 2 := fun a b => if s(a, b) = e then 1 else 0

/-- Without two-cells, the characteristic function of any edge is a wall label. -/
theorem isWallLabel_edgeLabel (hnosq : ∀ a b c d : Vx, ¬ S.sq a b c d) (e : Sym2 Vx) :
    S.IsWallLabel (edgeLabel e) where
  symm a b := by
    simp only [edgeLabel]
    rw [Sym2.eq_swap]
  square {a b c d} h := absurd h (hnosq a b c d)

/-- **The crossing number counts the uses of the edge.**  Along a walk of the one-skeleton, the
crossing number of the characteristic function of an edge `e` is, modulo two, the number of
times the walk traverses `e`. -/
theorem crossings_support (e : Sym2 Vx) :
    ∀ {u v : Vx} (p : (toSimpleGraph S).Walk u v),
      crossings (edgeLabel e) p.support = (p.edges.count e : ZMod 2) := by
  intro u v p
  induction p with
  | nil => simp
  | @cons a b c hadj q ih =>
      rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.edges_cons]
      rw [SimpleGraph.Walk.support_eq_cons q] at ih ⊢
      rw [crossings_cons_cons, ih, List.count_cons]
      by_cases h : s(a, b) = e
      · simp [edgeLabel, h, add_comm]
      · simp [edgeLabel, h]

/-- **A simply connected square complex without two-cells has an acyclic one-skeleton.** -/
theorem isAcyclic_of_simplyConnected (hnosq : ∀ a b c d : Vx, ¬ S.sq a b c d)
    (hSC : S.SimplyConnected) : (toSimpleGraph S).IsAcyclic := by
  intro v c hc
  -- the first edge of the cycle
  cases c with
  | nil => exact hc.ne_nil rfl
  | @cons _ b _ hadj q =>
      set e : Sym2 Vx := s(v, b) with he
      have hwalk : S.IsWalk (SimpleGraph.Walk.cons hadj q).support :=
        (SimpleGraph.Walk.cons hadj q).isChain_adj_support
      have hhead : (SimpleGraph.Walk.cons hadj q).support.head? = some v := by
        rw [SimpleGraph.Walk.support_cons]
        rfl
      have hlast : (SimpleGraph.Walk.cons hadj q).support.getLast? = some v := by
        rw [List.getLast?_eq_some_getLast (SimpleGraph.Walk.support_ne_nil _),
          SimpleGraph.Walk.getLast_support]
      have hclosed : S.IsClosedWalk v (SimpleGraph.Walk.cons hadj q).support :=
        ⟨hwalk, hhead, hlast⟩
      have hzero := crossings_eq_zero_of_closed hSC (isWallLabel_edgeLabel hnosq e) hclosed
      rw [crossings_support e] at hzero
      have hmem : e ∈ (SimpleGraph.Walk.cons hadj q).edges := by
        rw [SimpleGraph.Walk.edges_cons]
        exact List.mem_cons_self
      have hcount : (SimpleGraph.Walk.cons hadj q).edges.count e = 1 :=
        List.count_eq_one_of_mem hc.edges_nodup hmem
      rw [hcount] at hzero
      exact absurd hzero (by decide)

/-- **The one-dimensional case of Gromov's criterion, first half**: a connected, simply
connected square complex with no two-cells has a tree as one-skeleton. -/
theorem isTree_of_simplyConnected (hnosq : ∀ a b c d : Vx, ¬ S.sq a b c d)
    (hSC : S.SimplyConnected) (hconn : (toSimpleGraph S).Connected) :
    (toSimpleGraph S).IsTree :=
  ⟨hconn, isAcyclic_of_simplyConnected hnosq hSC⟩

open Classical in
/-- **The one-dimensional case of Gromov's criterion**: the one-skeleton of a connected, simply
connected square complex without two-cells is a median graph. -/
noncomputable def medianSimpleGraph_of_simplyConnected (hnosq : ∀ a b c d : Vx, ¬ S.sq a b c d)
    (hSC : S.SimplyConnected) (hconn : (toSimpleGraph S).Connected) (base : Vx) :
    MedianSimpleGraph Vx :=
  Tree.toMedianSimpleGraph (isTree_of_simplyConnected hnosq hSC hconn) base

theorem medianSimpleGraph_of_simplyConnected_adj (hnosq : ∀ a b c d : Vx, ¬ S.sq a b c d)
    (hSC : S.SimplyConnected) (hconn : (toSimpleGraph S).Connected) (base a b : Vx) :
    (medianSimpleGraph_of_simplyConnected hnosq hSC hconn base).G.Adj a b ↔ S.adj a b :=
  Iff.rfl

end SquareComplex

end FiniteChains
