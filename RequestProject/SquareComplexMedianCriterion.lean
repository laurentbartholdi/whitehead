module

public import RequestProject.SquareComplexHyperplane
public import RequestProject.SquareComplexCovering
public import RequestProject.GraphQuadrangleMedian
public import RequestProject.MedianGraphMetric

@[expose] public section

/-!
# From the quadrangle condition and convex halfspaces to a median one-skeleton

Gromov's criterion — *a simply connected square complex with flag links has median one-skeleton* —
is here reduced to two classical combinatorial statements about the one-skeleton `G` of a
connected, simply connected square complex `S`:

* the **quadrangle condition** `FiniteChains.QuadrangleCondition G` (proved to produce medians in
  `RequestProject/GraphQuadrangleMedian.lean`), and
* **convexity of the halfspaces** of the hyperplanes,
  `FiniteChains.SquareComplex.HalfspaceConvex` — a vertex on a geodesic between two vertices lying
  on the same side of a hyperplane lies on that side too.  This is the standard nonpositive
  curvature input; `RequestProject/SquareComplexWallsSphere.lean` shows that some such input is
  unavoidable, and `RequestProject/MedianHalfspaces.lean` proves it for median graphs.

What this file adds:

* `FiniteChains.SquareComplex.metricBipartite_of_simplyConnected` — a simply connected square
  complex has a bipartite one-skeleton, in the metric form required by the quadrangle argument
  (no extra hypothesis: it is the parity invariant of the wall label "all edges");
* `FiniteChains.SquareComplex.hyp_separation_of_convex` — convex halfspaces separate distinct
  vertices;
* `FiniteChains.SquareComplex.median_unique_of_convex` — convex halfspaces make medians unique:
  on every hyperplane a median must agree with the majority of the three vertices;
* `FiniteChains.SquareComplex.medianSimpleGraph_of_criterion` — **the conclusion of Gromov's
  criterion**: the one-skeleton is a median graph, given the quadrangle condition, convex
  halfspaces and the dimension bound of `FiniteChains.MedianSimpleGraph`.

Non-vacuity is checked at the end on the one-point complex.
-/

namespace FiniteChains

namespace SquareComplex

universe u

variable {Vx : Type u} {S : SquareComplex Vx} {G : SimpleGraph Vx}

section Compatible

variable (hadj : ∀ a b : Vx, S.adj a b ↔ G.Adj a b)

include hadj

/-- The support of a graph walk is a walk of the complex (the general statement is
`FiniteChains.SquareComplex.isWalkFrom_support`). -/
theorem isWalkFrom_support_of_adj {u v : Vx} (p : G.Walk u v) : S.IsWalkFrom u v p.support :=
  isWalkFrom_support (fun a b h => (hadj a b).mpr h) p

/-- A connected one-skeleton makes the complex connected in the sense used by the wall
machinery. -/
theorem walkConnected_of_adj_connected (hconn : G.Connected) (x₀ : Vx) :
    ∀ v : Vx, ∃ l, S.IsWalkFrom x₀ v l :=
  fun v => walkConnected_of_connected (fun a b h => (hadj a b).mpr h) hconn x₀ v

/-- **A simply connected square complex is bipartite**, in the metric form: the two endpoints of
an edge are at different distances from every vertex.  The parity of the length of a closed walk
is the crossing number of the wall label "all edges", so it vanishes. -/
theorem metricBipartite_of_simplyConnected (hSC : S.SimplyConnected) (hconn : G.Connected) :
    MetricBipartite G := by
  intro x u v huv heq
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x u
  obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_dist x v
  set w : G.Walk x x := p.append (SimpleGraph.Walk.cons huv q.reverse) with hw
  have hlen : w.length = G.dist x u + G.dist x v + 1 := by
    simp [hw, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons, hp, hq]
    omega
  have hclosed : S.IsClosedWalk x w.support := isWalkFrom_support_of_adj hadj w
  have hodd := closed_walk_length_odd hSC hclosed
  rw [SimpleGraph.Walk.length_support, hlen, heq] at hodd
  have : ((G.dist x v + G.dist x v + 1 + 1 : ℕ) : ZMod 2) = 0 := by
    have h2 : (G.dist x v + G.dist x v + 1 + 1 : ℕ) = 2 * (G.dist x v + 1) := by ring
    rw [h2, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  rw [this] at hodd
  exact zero_ne_one hodd

/-- A walk of the complex is at least as long as the distance in the one-skeleton. -/
theorem dist_le_of_walk_graph (hconn : G.Connected) :
    ∀ (l : List Vx) (u v : Vx), S.IsWalkFrom u v l → G.dist u v + 1 ≤ l.length := by
  intro l
  induction l with
  | nil => intro u v h; exact absurd h.2.1 (by simp)
  | cons p t ih =>
      intro u v h
      obtain ⟨hw, hhead, hlast⟩ := h
      have hpu : p = u := by simpa using hhead
      subst hpu
      match t with
      | [] =>
          have hpv : p = v := by simpa using hlast
          subst hpv
          simp [SimpleGraph.dist_self]
      | q :: t' =>
          have hpq : S.adj p q := (List.isChain_cons_cons.mp hw).1
          have hw' : S.IsWalk (q :: t') := (List.isChain_cons_cons.mp hw).2
          have hlast' : (q :: t').getLast? = some v := by simpa using hlast
          have hih := ih q v ⟨hw', by simp, hlast'⟩
          have hd1 : G.dist p q = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((hadj p q).mp hpq)
          have htri : G.dist p v ≤ G.dist p q + G.dist q v := hconn.dist_triangle
          simp only [List.length_cons] at hih ⊢
          omega

end Compatible

/-- Crossing counts add along a concatenation of walks. -/
theorem crossCount_glue (χ : Vx → Vx → ZMod 2) {v : Vx} :
    ∀ {l m : List Vx}, l.getLast? = some v → m.head? = some v →
      crossCount χ (l ++ m.tail) = crossCount χ l + crossCount χ m := by
  intro l
  induction l with
  | nil => intro m hl _; simp at hl
  | cons a l ih =>
      intro m hl hm
      match l with
      | [] =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hl
          subst hl
          match m with
          | [] => simp at hm
          | b :: t =>
              simp only [List.head?_cons, Option.some.injEq] at hm
              subst hm
              simp
      | b :: l' =>
          have hl' : (b :: l').getLast? = some v := by simpa using hl
          have := ih hl' hm
          simp only [List.cons_append, crossCount_cons_cons]
          rw [show (b :: l') ++ m.tail = b :: (l' ++ m.tail) from rfl] at this
          rw [this]
          ring

/-- **Convexity of the halfspaces of the hyperplanes**: a vertex on a geodesic between two
vertices on the same side of a hyperplane lies on that side.  This is the combinatorial form of
nonpositive curvature used below; it is equivalent to the statement that a geodesic crosses each
hyperplane at most once. -/
def HalfspaceConvex (G : SimpleGraph Vx) (σ : S.Hyp → Vx → ZMod 2) : Prop :=
  ∀ (H : S.Hyp) (a b z : Vx), σ H a = σ H b → G.dist a z + G.dist z b = G.dist a b →
    σ H z = σ H a

variable (hadj : ∀ a b : Vx, S.adj a b ↔ G.Adj a b)

include hadj

/-- **The crossing criterion gives convex halfspaces.**  If a shortest walk crosses every
hyperplane at most once — the form in which nonpositive curvature is used in
`RequestProject/SquareComplexWallsSeparation.lean` — then the halfspaces of the hyperplanes are
convex. -/
theorem halfspaceConvex_of_geodesic_crossings (hconn : G.Connected) {σ : S.Hyp → Vx → ZMod 2}
    (hσ : ∀ (H : S.Hyp) (u v : Vx), S.adj u v → σ H u + σ H v = S.hypLabel H u v)
    (hgeo : ∀ (u v : Vx) (l : List Vx), S.IsGeodesic u v l →
      ∀ H : S.Hyp, crossCount (S.hypLabel H) l ≤ 1) :
    HalfspaceConvex (S := S) G σ := by
  intro H a b z hab hbetween
  by_contra hne
  have hone : ∀ c d : ZMod 2, c ≠ d → c + d = 1 := by decide
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist a z
  obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_dist z b
  have hl1 : S.IsWalkFrom a z p.support := isWalkFrom_support_of_adj hadj p
  have hl2 : S.IsWalkFrom z b q.support := isWalkFrom_support_of_adj hadj q
  have hlsum : S.IsWalkFrom a b (p.append q).support :=
    isWalkFrom_support_of_adj hadj (p.append q)
  have hsupp : (p.append q).support = p.support ++ q.support.tail :=
    SimpleGraph.Walk.support_append p q
  have hlen : (p.append q).support.length = G.dist a b + 1 := by
    rw [SimpleGraph.Walk.length_support, SimpleGraph.Walk.length_append, hp, hq, hbetween]
  -- the concatenation is a shortest walk
  have hgeod : S.IsGeodesic a b (p.append q).support := by
    refine ⟨hlsum, fun m hm => ?_⟩
    have := dist_le_of_walk_graph hadj hconn m a b hm
    omega
  -- each half crosses the hyperplane an odd number of times
  have hcross1 : 1 ≤ crossCount (S.hypLabel H) p.support := by
    have hcr : crossings (S.hypLabel H) p.support = σ H a + σ H z :=
      crossings_eq_side (hσ H) _ a z hl1
    have hcast := crossCount_cast (S.hypLabel H) p.support
    rw [hcr, hone _ _ (Ne.symm hne)] at hcast
    rcases Nat.eq_zero_or_pos (crossCount (S.hypLabel H) p.support) with h0 | h0
    · rw [h0] at hcast; simp at hcast
    · omega
  have hcross2 : 1 ≤ crossCount (S.hypLabel H) q.support := by
    have hcr : crossings (S.hypLabel H) q.support = σ H z + σ H b :=
      crossings_eq_side (hσ H) _ z b hl2
    have hzb : σ H z ≠ σ H b := by rw [← hab]; exact hne
    rw [hone _ _ hzb] at hcr
    have hcast := crossCount_cast (S.hypLabel H) q.support
    rw [hcr] at hcast
    rcases Nat.eq_zero_or_pos (crossCount (S.hypLabel H) q.support) with h0 | h0
    · rw [h0] at hcast; simp at hcast
    · omega
  have hglue : crossCount (S.hypLabel H) (p.append q).support =
      crossCount (S.hypLabel H) p.support + crossCount (S.hypLabel H) q.support := by
    rw [hsupp]
    exact crossCount_glue (v := z) (S.hypLabel H) hl1.2.2 hl2.2.1
  have hle := hgeo a b _ hgeod H
  omega

/-- **Convex halfspaces separate.**  If the halfspaces of the hyperplanes are convex then distinct
vertices lie on different sides of some hyperplane. -/
theorem hyp_separation_of_convex (hconn : G.Connected) {σ : S.Hyp → Vx → ZMod 2}
    (hσ : ∀ (H : S.Hyp) (u v : Vx), S.adj u v → σ H u + σ H v = S.hypLabel H u v)
    (hconv : HalfspaceConvex (S := S) G σ) {u v : Vx} (huv : u ≠ v) :
    ∃ H : S.Hyp, σ H u ≠ σ H v := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, G.dist u v = n + 1 := by
    have hpos : 0 < G.dist u v := hconn.pos_dist_of_ne huv
    exact ⟨G.dist u v - 1, by omega⟩
  obtain ⟨w, huw, hwv⟩ := exists_adj_dist_pred hconn hn
  have hSadj : S.adj u w := (hadj u w).mpr huw
  refine ⟨S.hypOf u w, ?_⟩
  intro hcon
  have hbetween : G.dist u w + G.dist w v = G.dist u v := by
    rw [hwv, hn, SimpleGraph.dist_eq_one_iff_adj.mpr huw]
    omega
  have hw' : σ (S.hypOf u w) w = σ (S.hypOf u w) u := hconv _ u v w hcon hbetween
  have hside := hσ (S.hypOf u w) u w hSadj
  rw [hypLabel_self hSadj, hw'] at hside
  have h2 : ∀ c : ZMod 2, c + c ≠ 1 := by decide
  exact h2 _ hside

/-- **Medians are unique when the halfspaces are convex.**  On every hyperplane at least two of
the three vertices agree, and a median must agree with them; two medians therefore lie on the same
side of every hyperplane, hence coincide. -/
theorem median_unique_of_convex (hconn : G.Connected) {σ : S.Hyp → Vx → ZMod 2}
    (hσ : ∀ (H : S.Hyp) (u v : Vx), S.adj u v → σ H u + σ H v = S.hypLabel H u v)
    (hconv : HalfspaceConvex (S := S) G σ) {a b c z z' : Vx}
    (hz : IsMedianOf G a b c z) (hz' : IsMedianOf G a b c z') : z = z' := by
  by_contra hne
  obtain ⟨H, hH⟩ := hyp_separation_of_convex hadj hconn hσ hconv hne
  have h3 : ∀ x y w : ZMod 2, x = y ∨ y = w ∨ x = w := by decide
  refine hH ?_
  rcases h3 (σ H a) (σ H b) (σ H c) with hab | hbc | hac
  · rw [hconv H a b z hab hz.1, hconv H a b z' hab hz'.1]
  · have e1 : G.dist b z + G.dist z c = G.dist b c := hz.2.1
    have e2 : G.dist b z' + G.dist z' c = G.dist b c := hz'.2.1
    rw [hconv H b c z hbc e1, hconv H b c z' hbc e2]
  · rw [hconv H a c z hac hz.2.2, hconv H a c z' hac hz'.2.2]

/-- **Unique medians.**  In a connected, simply connected square complex whose one-skeleton
satisfies the quadrangle condition and whose hyperplane halfspaces are convex, every triple of
vertices has exactly one median.  This is the conclusion of Gromov's criterion, stated without the
dimension bound carried by `FiniteChains.MedianSimpleGraph`. -/
theorem existsUnique_median_of_criterion (hSC : S.SimplyConnected) (hconn : G.Connected)
    (hQC : QuadrangleCondition G) {σ : S.Hyp → Vx → ZMod 2}
    (hσ : ∀ (H : S.Hyp) (u v : Vx), S.adj u v → σ H u + σ H v = S.hypLabel H u v)
    (hconv : HalfspaceConvex (S := S) G σ) (a b c : Vx) :
    ∃! z : Vx, IsMedianOf G a b c z := by
  have hbip : MetricBipartite G := metricBipartite_of_simplyConnected hadj hSC hconn
  obtain ⟨z, hz⟩ := exists_median hconn hbip hQC a b c
  exact ⟨z, hz, fun z' hz' => median_unique_of_convex hadj hconn hσ hconv hz' hz⟩

/-- **The conclusion of Gromov's criterion.**  A connected, simply connected square complex whose
one-skeleton satisfies the quadrangle condition and whose hyperplane halfspaces are convex has a
median one-skeleton: every triple of vertices has a unique median.  (The dimension bound `dim_le`
of `FiniteChains.MedianSimpleGraph` is an extra hypothesis: it is the statement that the complex is
at most three dimensional, not part of the criterion.) -/
noncomputable def medianSimpleGraph_of_criterion (hSC : S.SimplyConnected) (hconn : G.Connected)
    (hQC : QuadrangleCondition G) {σ : S.Hyp → Vx → ZMod 2}
    (hσ : ∀ (H : S.Hyp) (u v : Vx), S.adj u v → σ H u + σ H v = S.hypLabel H u v)
    (hconv : HalfspaceConvex (S := S) G σ) (base : Vx)
    (hdim : ∀ (w : Vx) (s : Finset Vx),
      (∀ a ∈ s, G.Adj a w ∧ G.dist base a + 1 = G.dist base w) → s.card ≤ 3) :
    MedianSimpleGraph Vx := by
  classical
  have hbip : MetricBipartite G := metricBipartite_of_simplyConnected hadj hSC hconn
  have hex : ∀ a b c : Vx, ∃ z : Vx, IsMedianOf G a b c z := exists_median hconn hbip hQC
  refine
    { G := G
      conn := hconn
      base := base
      med := fun a b c => Classical.choose (hex a b c)
      med_ab := fun a b c => (Classical.choose_spec (hex a b c)).1
      med_bc := fun a b c => (Classical.choose_spec (hex a b c)).2.1
      med_ac := fun a b c => (Classical.choose_spec (hex a b c)).2.2
      med_unique := ?_
      dim_le := hdim }
  intro a b c z h1 h2 h3
  exact median_unique_of_convex hadj hconn hσ hconv ⟨h1, h2, h3⟩ (Classical.choose_spec (hex a b c))

end SquareComplex

end FiniteChains
