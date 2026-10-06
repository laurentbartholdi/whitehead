module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Tactic

@[expose] public section

/-!
# The quadrangle condition produces medians

This file proves one half of the combinatorial content of Gromov's criterion, purely
graph-theoretically and with no curvature assumption beyond the two stated conditions:

* `FiniteChains.MetricBipartite` — adjacent vertices are at different distances from every
  vertex (the metric form of bipartiteness);
* `FiniteChains.QuadrangleCondition` — two distinct neighbours `u, v` of a vertex `q`, both one
  step closer to `x` than `q` is, have a common neighbour one further step closer to `x`.

The main result `FiniteChains.exists_median` says that in a connected graph with these two
properties **every triple of vertices has a median**, i.e. the graph is *modular*.  Uniqueness of
the median is a separate matter, supplied in
`RequestProject/SquareComplexMedianCriterion.lean` by the halfspaces of the hyperplanes.

The proof is an induction on `d(b, c)`.  Either some neighbour of `b` on a geodesic towards `c`
is also closer to `a` — and then the median of the smaller triple is a median of the original one
(`FiniteChains.IsMedianOf.step`) — or every such neighbour is farther from `a`, and then the
quadrangle condition propagates this to the whole geodesic, so `d(a, c) = d(a, b) + d(b, c)` and
`b` itself is the median (`FiniteChains.dist_add_of_gate`).
-/

namespace FiniteChains

universe u

variable {Vx : Type u} {G : SimpleGraph Vx}

/-- The metric form of bipartiteness: the two endpoints of an edge are never at the same distance
from a vertex. -/
def MetricBipartite (G : SimpleGraph Vx) : Prop :=
  ∀ x u v : Vx, G.Adj u v → G.dist x u ≠ G.dist x v

/-- The **quadrangle condition**: two distinct neighbours `u, v` of a vertex `q`, each one step
closer to `x` than `q` is, have a common neighbour one further step closer to `x`. -/
def QuadrangleCondition (G : SimpleGraph Vx) : Prop :=
  ∀ x q u v : Vx, G.Adj u q → G.Adj v q → u ≠ v →
    G.dist x u + 1 = G.dist x q → G.dist x v + 1 = G.dist x q →
      ∃ w : Vx, G.Adj w u ∧ G.Adj w v ∧ G.dist x w + 2 = G.dist x q

/-- `z` is a **median** of `a`, `b`, `c`: it lies on a geodesic between each pair. -/
def IsMedianOf (G : SimpleGraph Vx) (a b c z : Vx) : Prop :=
  G.dist a z + G.dist z b = G.dist a b ∧
    G.dist b z + G.dist z c = G.dist b c ∧
      G.dist a z + G.dist z c = G.dist a c

/-- **The quadrangle condition is automatic at distance at most two**: the required common
neighbour is then `x` itself.  The content of the condition therefore starts at distance three,
which is where the link condition of a nonpositively curved complex is needed. -/
theorem quadrangle_of_dist_le_two (hconn : G.Connected) {x q u v : Vx} (huv : u ≠ v)
    (hlu : G.dist x u + 1 = G.dist x q) (hlv : G.dist x v + 1 = G.dist x q)
    (hle : G.dist x q ≤ 2) :
    ∃ w : Vx, G.Adj w u ∧ G.Adj w v ∧ G.dist x w + 2 = G.dist x q := by
  have hq1 : G.dist x q ≠ 1 := by
    intro h
    have hu0 : G.dist x u = 0 := by omega
    have hv0 : G.dist x v = 0 := by omega
    exact huv (((hconn.dist_eq_zero_iff).mp hu0).symm.trans ((hconn.dist_eq_zero_iff).mp hv0))
  have hq0 : G.dist x q ≠ 0 := by omega
  have hq2 : G.dist x q = 2 := by omega
  refine ⟨x, ?_, ?_, by simp [hq2]⟩
  · exact SimpleGraph.dist_eq_one_iff_adj.mp (by omega)
  · exact SimpleGraph.dist_eq_one_iff_adj.mp (by omega)

/-- A neighbour one step closer: if `b` and `c` are at distance `n + 1` then some neighbour of
`b` is at distance `n` from `c`. -/
theorem exists_adj_dist_pred (hconn : G.Connected) {b c : Vx} {n : ℕ} (h : G.dist b c = n + 1) :
    ∃ u : Vx, G.Adj b u ∧ G.dist u c = n := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist b c
  cases p with
  | nil => simp only [SimpleGraph.Walk.length_nil] at hp; omega
  | @cons _ y _ hadj q =>
      refine ⟨y, hadj, le_antisymm ?_ ?_⟩
      · have := SimpleGraph.dist_le q
        rw [SimpleGraph.Walk.length_cons, h] at hp
        omega
      · have htri := (hconn.dist_triangle (u := b) (v := y) (w := c))
        have h1 : G.dist b y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
        rw [h1, h] at htri
        omega

/-- **Transporting a median one step.**  If `u` is a neighbour of `b` one step closer to both `a`
and `c`, then a median of `a, u, c` is a median of `a, b, c`. -/
theorem IsMedianOf.step {a b c u m : Vx} (hconn : G.Connected) (hm : IsMedianOf G a u c m)
    (hbu : G.Adj b u) (hau : G.dist a u + 1 = G.dist a b)
    (huc : G.dist u c + 1 = G.dist b c) : IsMedianOf G a b c m := by
  obtain ⟨h1, h2, h3⟩ := hm
  have hbu1 : G.dist b u = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hbu
  have hub1 : G.dist u b = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hbu.symm
  have hmu : G.dist m u = G.dist u m := SimpleGraph.dist_comm
  have hmb : G.dist m b = G.dist b m := SimpleGraph.dist_comm
  -- `m` is one step farther from `b` than from `u`
  have hle : G.dist b m ≤ G.dist u m + 1 := by
    have := hconn.dist_triangle (u := b) (v := u) (w := m)
    omega
  have hge : G.dist u m + 1 ≤ G.dist b m := by
    have := hconn.dist_triangle (u := a) (v := m) (w := b)
    omega
  have hbm : G.dist b m = G.dist u m + 1 := le_antisymm hle hge
  refine ⟨by omega, by omega, h3⟩

/-- **The gate lemma.**  If no neighbour of `b` on a geodesic towards `c` is closer to `a`, then
the quadrangle condition forces `d(a, c) = d(a, b) + d(b, c)`. -/
theorem dist_add_of_gate (hconn : G.Connected) (hbip : MetricBipartite G)
    (hQC : QuadrangleCondition G) :
    ∀ (n : ℕ) (a b c : Vx), G.dist b c = n →
      (∀ u : Vx, G.Adj b u → G.dist u c + 1 = n → G.dist a u = G.dist a b + 1) →
        G.dist a c = G.dist a b + n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b c hbc hgate
    match n with
    | 0 =>
        have : b = c := (hconn.dist_eq_zero_iff).mp hbc
        subst this
        simp
    | (m + 1) =>
        obtain ⟨u, hbu, huc⟩ := exists_adj_dist_pred hconn hbc
        have hau : G.dist a u = G.dist a b + 1 := hgate u hbu (by omega)
        -- the same hypothesis holds one step further along
        have hgate' : ∀ u' : Vx, G.Adj u u' → G.dist u' c + 1 = m →
            G.dist a u' = G.dist a u + 1 := by
          intro u' huu' hu'c
          have hdiff := (huu'.diff_dist_adj (u := a))
          have hne := hbip a u u' huu'
          -- either `u'` is farther from `a` (what we want) or one step closer
          rcases hdiff with h | h | h
          · exact absurd h.symm hne
          · exact h
          · exfalso
            -- `u'` one step closer to `a` than `u`
            have hau' : G.dist a u' + 1 = G.dist a u := by
              have hle : G.dist a u' ≤ G.dist a u + 1 := by
                have := hconn.dist_triangle (u := a) (v := u) (w := u')
                have : G.dist u u' = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr huu'
                omega
              have hpos : G.dist a u ≠ 0 := by
                intro h0
                have : a = u := (hconn.dist_eq_zero_iff).mp h0
                subst this
                have h1 : G.dist a u' = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr huu'
                omega
              omega
            have hu'b : u' ≠ b := by
              intro h
              subst h
              omega
            have habu : G.dist a b + 1 = G.dist a u := by omega
            obtain ⟨w, hwb, hwu', hw⟩ :=
              hQC a u b u' hbu huu'.symm (Ne.symm hu'b) habu hau'
            have hwb1 : G.dist w b = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hwb
            have hbw1 : G.dist b w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hwb.symm
            have hwu'1 : G.dist w u' = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hwu'
            have hwcle : G.dist w c ≤ m := by
              have := hconn.dist_triangle (u := w) (v := u') (w := c)
              omega
            have hwcge : m ≤ G.dist w c := by
              have := hconn.dist_triangle (u := b) (v := w) (w := c)
              omega
            have hwc : G.dist w c = m := le_antisymm hwcle hwcge
            have := hgate w hwb.symm (by omega)
            omega
        have hrec : G.dist a c = G.dist a u + m :=
          ih m (by omega) a u c huc hgate'
        omega

/-- **Medians exist.**  A connected graph which is bipartite in the metric sense and satisfies the
quadrangle condition is modular: every triple of vertices has a median. -/
theorem exists_median (hconn : G.Connected) (hbip : MetricBipartite G)
    (hQC : QuadrangleCondition G) (a b c : Vx) : ∃ z : Vx, IsMedianOf G a b c z := by
  suffices h : ∀ (n : ℕ) (a b c : Vx), G.dist b c = n → ∃ z : Vx, IsMedianOf G a b c z from
    h (G.dist b c) a b c rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b c hbc
    match n with
    | 0 =>
        have hb : b = c := (hconn.dist_eq_zero_iff).mp hbc
        subst hb
        exact ⟨b, by simp [IsMedianOf]⟩
    | (m + 1) =>
        by_cases hsome : ∃ u : Vx, G.Adj b u ∧ G.dist u c + 1 = m + 1 ∧
            G.dist a u + 1 = G.dist a b
        · obtain ⟨u, hbu, huc, hau⟩ := hsome
          obtain ⟨z, hz⟩ := ih m (by omega) a u c (by omega)
          exact ⟨z, hz.step hconn hbu hau (by omega)⟩
        · push_neg at hsome
          have hgate : ∀ u : Vx, G.Adj b u → G.dist u c + 1 = m + 1 →
              G.dist a u = G.dist a b + 1 := by
            intro u hbu huc
            have hne : G.dist a u + 1 ≠ G.dist a b := hsome u hbu huc
            have hdiff := (hbu.diff_dist_adj (u := a))
            have hbip' := hbip a b u hbu
            have hle : G.dist a u ≤ G.dist a b + 1 := by
              have := hconn.dist_triangle (u := a) (v := b) (w := u)
              have h1 : G.dist b u = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hbu
              omega
            have hle' : G.dist a b ≤ G.dist a u + 1 := by
              have := hconn.dist_triangle (u := a) (v := u) (w := b)
              have h1 : G.dist u b = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hbu.symm
              omega
            omega
          have hac : G.dist a c = G.dist a b + (m + 1) :=
            dist_add_of_gate hconn hbip hQC (m + 1) a b c hbc hgate
          refine ⟨b, ?_, ?_, ?_⟩ <;> simp only [SimpleGraph.dist_self, add_zero, zero_add, hbc,
            hac]

end FiniteChains
