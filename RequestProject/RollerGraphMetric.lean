import RequestProject.CubeRollerMedian
import RequestProject.MedianGraphMetric
import RequestProject.RollerConnected

/-!
# The Roller model as an actual graph

`RequestProject/CubeRollerMedian.lean` shows that the vertex set of a median-closed Roller
model, with the distance `dsym A B = |A \ B| + |B \ A|` counting the separating hyperplanes, is
a `FiniteChains.MedianGraph`: a metric with unique medians.  As `RequestProject/RollerConnected.lean`
records, median-closedness alone does not make that metric the edge metric of a graph — the
median-closed set `{∅, {p, q}}` has no one-coordinate path between its two vertices.

This file adds the hypothesis that makes the model a genuine graph and proves the resulting
statement.  A `FiniteChains.GatedRollerModel` is a Roller model in which, for any two distinct
vertices `A ≠ B`, some vertex `C` of the model is obtained from `A` by changing one coordinate
and is one step closer to `B` (a *gate* step towards `B`).  Then:

* `FiniteChains.GatedRollerModel.graph` — the graph whose edges are the pairs of vertices
  differing in exactly one hyperplane;
* `FiniteChains.GatedRollerModel.dist_eq_dsym` — the graph distance of that graph is exactly
  the number of separating hyperplanes, so `dsym` is the edge metric;
* `FiniteChains.GatedRollerModel.connected` — the graph is connected;
* `FiniteChains.GatedRollerModel.toMedianSimpleGraph` — the model is a median graph in the
  graph-theoretic sense of `RequestProject/MedianGraphMetric.lean`;
* `FiniteChains.GatedRollerModel.ker_d₂_eq_range_d₃` — hence `ker d₂ = im d₃` for the cellular
  chains, with all the cells being genuine cubes of that graph.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open RollerBridge

universe u

variable {ι : Type u} [DecidableEq ι]

/-- A **gated Roller model**: a median-closed Roller model in which one can always move one
step towards another vertex by changing a single coordinate.  This is what makes the counting
distance `dsym` the edge metric of a connected graph. -/
structure GatedRollerModel (ι : Type u) [DecidableEq ι] extends RollerModel ι where
  /-- From any vertex one can step towards any other vertex, changing one coordinate. -/
  step : ∀ {A B : Finset ι}, A ∈ toRollerModel.W → B ∈ toRollerModel.W → A ≠ B →
    ∃ C ∈ toRollerModel.W, dsym A C = 1 ∧ dsym C B + 1 = dsym A B

namespace GatedRollerModel

variable (M : GatedRollerModel ι)

/-- The graph of the model: two vertices are adjacent when they differ in exactly one
hyperplane. -/
def graph : SimpleGraph M.Vtx where
  Adj u v := dsym u.1 v.1 = 1
  symm := ⟨fun u v h => by rwa [dsym_comm]⟩
  loopless := ⟨fun u h => by
    have h' : dsym u.1 u.1 = 1 := h
    rw [dsym_self] at h'
    exact Nat.zero_ne_one h'⟩

@[simp] theorem graph_adj {u v : M.Vtx} : (M.graph).Adj u v ↔ dsym u.1 v.1 = 1 := Iff.rfl

/-- Between any two vertices there is a walk whose length is the number of separating
hyperplanes. -/
theorem exists_walk (n : ℕ) : ∀ u v : M.Vtx, dsym u.1 v.1 = n →
    ∃ p : (M.graph).Walk u v, p.length = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u v h
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · have huv : u = v := Subtype.ext (eq_of_dsym_eq_zero h)
      subst huv
      exact ⟨SimpleGraph.Walk.nil, rfl⟩
    · have hne : u.1 ≠ v.1 := by
        intro e
        rw [e, dsym_self] at h
        omega
      obtain ⟨C, hC, h1, h2⟩ := M.step u.2 v.2 hne
      have hadj : (M.graph).Adj u ⟨C, hC⟩ := h1
      obtain ⟨p, hp⟩ := ih (dsym C v.1) (by omega) ⟨C, hC⟩ v rfl
      refine ⟨SimpleGraph.Walk.cons hadj p, ?_⟩
      rw [SimpleGraph.Walk.length_cons, hp]
      omega

/-- The number of separating hyperplanes is a lower bound for the length of any walk. -/
theorem dsym_le_length {u v : M.Vtx} (p : (M.graph).Walk u v) : dsym u.1 v.1 ≤ p.length := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
      have htri := dsym_triangle x.1 y.1 z.1
      have hadj : dsym x.1 y.1 = 1 := h
      rw [SimpleGraph.Walk.length_cons]
      omega

/-- **The counting distance is the graph distance**: `dsym` is the edge metric of the graph of
the model. -/
theorem dist_eq_dsym (u v : M.Vtx) : (M.graph).dist u v = dsym u.1 v.1 := by
  obtain ⟨p, hp⟩ := M.exists_walk (dsym u.1 v.1) u v rfl
  have h1 : (M.graph).dist u v ≤ dsym u.1 v.1 := hp ▸ SimpleGraph.dist_le p
  obtain ⟨q, hq⟩ := SimpleGraph.Reachable.exists_walk_length_eq_dist (G := M.graph) ⟨p⟩
  have h2 := M.dsym_le_length q
  omega

/-- **The graph of a gated Roller model is connected.** -/
theorem connected : (M.graph).Connected := by
  haveI : Nonempty M.Vtx := ⟨⟨∅, M.base_mem⟩⟩
  refine SimpleGraph.Connected.mk ?_
  intro u v
  obtain ⟨p, -⟩ := M.exists_walk (dsym u.1 v.1) u v rfl
  exact ⟨p⟩

/-- **A gated Roller model is a median graph in the graph-theoretic sense**: its graph is
connected, its distance is the edge metric, and every triple of vertices has a unique median,
namely the majority vote. -/
def toMedianSimpleGraph : MedianSimpleGraph M.Vtx where
  G := M.graph
  conn := M.connected
  base := ⟨∅, M.base_mem⟩
  med := fun a b c => ⟨medFinset a.1 b.1 c.1, M.med_mem a.2 b.2 c.2⟩
  med_ab := by
    intro a b c
    simp only [M.dist_eq_dsym]
    exact (M.toRollerModel.toMedianGraph).med_ab a b c
  med_bc := by
    intro a b c
    simp only [M.dist_eq_dsym]
    exact (M.toRollerModel.toMedianGraph).med_bc a b c
  med_ac := by
    intro a b c
    simp only [M.dist_eq_dsym]
    exact (M.toRollerModel.toMedianGraph).med_ac a b c
  med_unique := by
    intro a b c z h₁ h₂ h₃
    simp only [M.dist_eq_dsym] at h₁ h₂ h₃
    exact (M.toRollerModel.toMedianGraph).med_unique a b c z h₁ h₂ h₃
  dim_le := by
    intro w s hs
    refine (M.toRollerModel.toMedianGraph).dim_le w s fun a ha => ?_
    obtain ⟨h1, h2⟩ := hs a ha
    rw [M.dist_eq_dsym, M.dist_eq_dsym] at h2
    exact ⟨h1, h2⟩

/-- **Every two-cycle bounds** in the cellular chain complex of a gated Roller model. -/
theorem ker_d₂_eq_range_d₃ :
    LinearMap.ker ((M.toMedianSimpleGraph).toDescCubeStr).d₂ =
      LinearMap.range ((M.toMedianSimpleGraph).toDescCubeStr).d₃ :=
  (M.toMedianSimpleGraph).ker_d₂_eq_range_d₃

end GatedRollerModel

end FiniteChains
