module

public import RequestProject.MedianGraphMetric

@[expose] public section

/-!
# Halfspaces of a median graph are convex

`RequestProject/CubeMedianGraph.lean` and `RequestProject/MedianGraphMetric.lean` derive the
descending-cube axioms — and hence `ker d₂ = im d₃` — from the hypothesis that the one-skeleton
of the complex is a median graph.  `RequestProject/SquareComplexWalls.lean` and
`RequestProject/WallSpaceDual.lean` develop the other half of Sageev's construction: the walls
(hyperplanes) of a square complex and the median dual complex of a wall space.  The two halves
are joined by the *separation* property — distinct vertices lie on different sides of some wall
— which `RequestProject/SquareComplexWallsSphere.lean` shows does **not** follow from simple
connectivity alone, and `RequestProject/SquareComplexWallsSeparation.lean` reduces to the
standard criterion "a shortest path crosses a wall at most once".

This file proves that criterion, unconditionally, in the nonpositively curved case, that is,
whenever the one-skeleton is a median graph.  Everything is elementary: the only inputs are the
metric axioms, the existence and uniqueness of medians, and the possibility of making one step
towards another vertex (`FiniteChains.MedianGraph.HasSteps`, automatic for the graph-theoretic
`FiniteChains.MedianSimpleGraph`).

For an edge `X–Y` write `Side X Y t` for "`t` is one step closer to `X` than to `Y`".  The
results are:

* `FiniteChains.MedianGraph.side_dichotomy` — every vertex lies on exactly one side of an edge;
* `FiniteChains.MedianGraph.side_of_between` — the `X`-side is star-shaped towards `X`;
* `FiniteChains.MedianGraph.crossing_dist` — an edge crossing the wall changes the distance to
  `X` by exactly one;
* `FiniteChains.MedianGraph.not_badConfig` — **the key theorem**: crossing the wall never gets
  closer to a vertex on the near side; proved by induction on the distance, the base case being
  an application of the *uniqueness* of medians (which is exactly what fails for `K₂,₃`);
* `FiniteChains.MedianGraph.side_convex` — hence the halfspaces of an edge are convex;
* `FiniteChains.MedianGraph.exists_separating_edge` — hence distinct vertices are separated by
  the wall of some edge.
-/

namespace FiniteChains

universe u

namespace MedianGraph

variable {Vx : Type u} {G : MedianGraph Vx}

/-- `t` lies on the `X`-side of the edge `X–Y`: it is one step closer to `X` than to `Y`. -/
def Side (G : MedianGraph Vx) (X Y t : Vx) : Prop := G.dist t Y = G.dist t X + 1

/-- The possibility of stepping towards another vertex.  This holds in any connected graph with
its edge metric; see `FiniteChains.MedianSimpleGraph.hasSteps`. -/
def HasSteps (G : MedianGraph Vx) : Prop :=
  ∀ a b : Vx, a ≠ b → ∃ c : Vx, G.dist a c = 1 ∧ G.dist c b + 1 = G.dist a b

/-- The median of a vertex with the two endpoints of an edge is one of those endpoints. -/
theorem med_edge {X Y : Vx} (hXY : G.dist X Y = 1) (t : Vx) :
    G.med t X Y = X ∨ G.med t X Y = Y := by
  have h1 := G.med_bc t X Y
  rw [hXY] at h1
  rcases Nat.eq_zero_or_pos (G.dist X (G.med t X Y)) with h0 | h0
  · exact Or.inl (G.eq_of_dist_eq_zero h0).symm
  · exact Or.inr (G.eq_of_dist_eq_zero (by omega))

/-- **Every vertex lies on one of the two sides of an edge.** -/
theorem side_dichotomy {X Y : Vx} (hXY : G.dist X Y = 1) (t : Vx) :
    G.Side X Y t ∨ G.Side Y X t := by
  rcases med_edge hXY t with hm | hm
  · left
    have h := G.med_ac t X Y
    rw [hm, hXY] at h
    exact h.symm
  · right
    have h := G.med_ab t X Y
    rw [hm, G.dist_comm Y X, hXY] at h
    exact h.symm

/-- A vertex cannot lie on both sides of an edge. -/
theorem not_side_both {X Y t : Vx} (h1 : G.Side X Y t) (h2 : G.Side Y X t) : False := by
  unfold Side at h1 h2; omega

/-- **The `X`-side is star-shaped towards `X`**: every vertex on a geodesic from a vertex of the
`X`-side to `X` lies on the `X`-side. -/
theorem side_of_between {X Y a w : Vx} (hXY : G.dist X Y = 1) (ha : G.Side X Y a)
    (hw : G.dist a w + G.dist w X = G.dist a X) : G.Side X Y w := by
  have t1 : G.dist w Y ≤ G.dist w X + G.dist X Y := G.dist_triangle w X Y
  have t2 : G.dist a Y ≤ G.dist a w + G.dist w Y := G.dist_triangle a w Y
  unfold Side at ha ⊢
  omega

/-- **An edge crossing the wall of `X–Y` changes the distance to `X` by one.** -/
theorem crossing_dist {X Y s t : Vx} (hst : G.dist s t = 1)
    (hs : G.Side X Y s) (ht : G.Side Y X t) : G.dist s X + 1 = G.dist t X := by
  have t1 : G.dist s Y ≤ G.dist s t + G.dist t Y := G.dist_triangle s t Y
  have t2 : G.dist t X ≤ G.dist t s + G.dist s X := G.dist_triangle t s X
  have hts : G.dist t s = 1 := by rw [G.dist_comm]; exact hst
  unfold Side at hs ht
  omega

/-- The configuration excluded by the main theorem: an edge `s–t` crossing the wall of `X–Y`,
with `s` on the same side as a vertex `h`, yet with `t` strictly closer to `h` than `s` is. -/
def BadConfig (G : MedianGraph Vx) (X Y s t h : Vx) : Prop :=
  G.dist s t = 1 ∧ G.Side X Y s ∧ G.Side Y X t ∧ G.Side X Y h ∧ G.dist t h + 1 = G.dist s h

/-- In a bad configuration of least size the far vertex `h` lies on a geodesic from `t`
to `X`. -/
theorem badConfig_between {X Y s t h : Vx} (hXY : G.dist X Y = 1)
    (hmin : ∀ s' t' h' : Vx, G.BadConfig X Y s' t' h' → G.dist s' h' < G.dist s h → False)
    (hc : G.BadConfig X Y s t h) : G.dist t h + G.dist h X = G.dist t X := by
  obtain ⟨hst, hs, ht, hh, hd⟩ := hc
  set q := G.med h t X with hq
  have e1 : G.dist h q + G.dist q t = G.dist h t := G.med_ab h t X
  have e2 : G.dist t q + G.dist q X = G.dist t X := G.med_bc h t X
  have e3 : G.dist h q + G.dist q X = G.dist h X := G.med_ac h t X
  have c1 : G.dist h t = G.dist t h := G.dist_comm h t
  have c2 : G.dist q t = G.dist t q := G.dist_comm q t
  have c3 : G.dist q h = G.dist h q := G.dist_comm q h
  have hqside : G.Side X Y q := side_of_between hXY hh e3
  -- the median of `s`, `t` and `q` is one of the endpoints of the edge `s–t`
  have hr : G.med s t q = s ∨ G.med s t q = t := by
    have h1 := G.med_ab s t q
    rw [hst] at h1
    rcases Nat.eq_zero_or_pos (G.dist s (G.med s t q)) with h0 | h0
    · exact Or.inl (G.eq_of_dist_eq_zero h0).symm
    · exact Or.inr (G.eq_of_dist_eq_zero (by omega))
  rcases hr with hr | hr
  · -- `s` between `t` and `q`: then `h` would be too close to `s`
    exfalso
    have h2 := G.med_bc s t q
    rw [hr, G.dist_comm t s, hst] at h2
    have h3 : G.dist s h ≤ G.dist s q + G.dist q h := G.dist_triangle s q h
    omega
  · -- `t` between `s` and `q`: a bad configuration with witness `q`
    have h2 := G.med_ac s t q
    rw [hr, hst] at h2
    have hqeq : q = h := by
      by_contra hne
      have hpos : 0 < G.dist h q := by
        rcases Nat.eq_zero_or_pos (G.dist h q) with h0 | h0
        · exact absurd (G.eq_of_dist_eq_zero h0).symm hne
        · exact h0
      exact hmin s t q ⟨hst, hs, ht, hqside, by omega⟩ (by omega)
    rw [hqeq] at e2
    exact e2

/-- **The key theorem**: in a median graph there is no bad configuration — crossing the wall of
an edge `X–Y` never gets closer to a vertex lying on the same side as the near endpoint.

The induction is on the distance `dist s h`; the base case `dist t h = 1` is where the
*uniqueness* of medians is used (and it is exactly this that fails for `K₂,₃`). -/
theorem not_badConfig {X Y : Vx} (hXY : G.dist X Y = 1) (hstep : G.HasSteps) :
    ∀ s t h : Vx, ¬ G.BadConfig X Y s t h := by
  intro s t h
  induction hn : G.dist s h using Nat.strong_induction_on generalizing s t h with
  | _ n ih =>
  subst hn
  rintro hc
  obtain ⟨hst, hs, ht, hh, hd⟩ := hc
  have hmin : ∀ s' t' h' : Vx, G.BadConfig X Y s' t' h' → G.dist s' h' < G.dist s h → False := by
    intro s' t' h' hc' hlt
    exact ih (G.dist s' h') hlt s' t' h' rfl hc'
  -- `t ≠ h`, since they lie on different sides
  have hth : t ≠ h := by
    rintro rfl
    exact not_side_both hh ht
  have hk : 1 ≤ G.dist t h := by
    rcases Nat.eq_zero_or_pos (G.dist t h) with h0 | h0
    · exact absurd (G.eq_of_dist_eq_zero h0) hth
    · exact h0
  -- `h` lies on a geodesic from `t` to `X`
  have hA : G.dist t h + G.dist h X = G.dist t X :=
    badConfig_between hXY hmin ⟨hst, hs, ht, hh, hd⟩
  have hB : G.dist s X + 1 = G.dist t X := crossing_dist hst hs ht
  -- one step from `h` towards `t`
  obtain ⟨h₁, hh₁, hh₁t⟩ := hstep h t (Ne.symm hth)
  have c1 : G.dist h t = G.dist t h := G.dist_comm h t
  have c2 : G.dist h s = G.dist s h := G.dist_comm h s
  have c3 : G.dist t s = G.dist s t := G.dist_comm t s
  have c4 : G.dist t h₁ = G.dist h₁ t := G.dist_comm t h₁
  have c5 : G.dist h₁ h = G.dist h h₁ := G.dist_comm h₁ h
  have c6 : G.dist h₁ s = G.dist s h₁ := G.dist_comm h₁ s
  -- either we find a smaller bad configuration, or the distance from `t` to `h` is one
  have hk1 : G.dist t h = 1 := by
    rcases side_dichotomy hXY h₁ with hside | hside
    · -- a bad configuration with the closer witness `h₁`
      exfalso
      have u1 : G.dist s h₁ ≤ G.dist s t + G.dist t h₁ := G.dist_triangle s t h₁
      have u2 : G.dist s h ≤ G.dist s h₁ + G.dist h₁ h := G.dist_triangle s h₁ h
      exact hmin s t h₁ ⟨hst, hs, ht, hside, by omega⟩ (by omega)
    · -- a bad configuration of the same size, with the crossing edge `h–h₁`
      have u1 : G.dist h₁ s ≤ G.dist h₁ t + G.dist t s := G.dist_triangle h₁ t s
      have u2 : G.dist h s ≤ G.dist h h₁ + G.dist h₁ s := G.dist_triangle h h₁ s
      have hc' : G.BadConfig X Y h h₁ s := ⟨hh₁, hh, hside, hs, by omega⟩
      have hmin' : ∀ s' t' h' : Vx, G.BadConfig X Y s' t' h' → G.dist s' h' < G.dist h s →
          False := fun s' t' h' hc'' hlt => hmin s' t' h' hc'' (by omega)
      have hA' : G.dist h₁ s + G.dist s X = G.dist h₁ X := badConfig_between hXY hmin' hc'
      have u3 : G.dist h₁ X ≤ G.dist h₁ h + G.dist h X := G.dist_triangle h₁ h X
      omega
  -- the remaining case: `t` is adjacent to `h`, and uniqueness of medians applies
  exfalso
  set p := G.med s h X with hp
  have f1 : G.dist s p + G.dist p h = G.dist s h := G.med_ab s h X
  have f2 : G.dist h p + G.dist p X = G.dist h X := G.med_bc s h X
  have f3 : G.dist s p + G.dist p X = G.dist s X := G.med_ac s h X
  have c7 : G.dist p h = G.dist h p := G.dist_comm p h
  have c8 : G.dist p s = G.dist s p := G.dist_comm p s
  have hsp : G.dist s p = 1 := by omega
  have hph : G.dist p h = 1 := by omega
  have hpX : G.dist p X + 1 = G.dist h X := by omega
  have hpside : G.Side X Y p := side_of_between hXY hs f3
  -- both `t` and `p` are medians of the triple `Y`, `s`, `h`
  have hYs : G.dist Y s = G.dist s X + 1 := by rw [G.dist_comm Y s]; exact hs
  have hYh : G.dist Y h = G.dist h X + 1 := by rw [G.dist_comm Y h]; exact hh
  have hYt : G.dist Y t + 1 = G.dist t X := by rw [G.dist_comm Y t]; exact ht.symm
  have hYp : G.dist Y p = G.dist p X + 1 := by rw [G.dist_comm Y p]; exact hpside
  have ht_med : t = G.med Y s h := by
    refine G.med_unique Y s h t ?_ ?_ ?_
    · omega
    · omega
    · omega
  have hp_med : p = G.med Y s h := by
    refine G.med_unique Y s h p ?_ ?_ ?_
    · omega
    · omega
    · omega
  have htp : t = p := by rw [ht_med, hp_med]
  rw [htp] at ht
  exact not_side_both hpside ht

/-- **No step across the wall gets closer to the near side**: if the edge `s–t` crosses the wall
of `X–Y` with `s` on the `X`-side, then `s` is at least as close as `t` to every vertex of the
`X`-side. -/
theorem side_dist_le {X Y s t h : Vx} (hXY : G.dist X Y = 1) (hstep : G.HasSteps)
    (hst : G.dist s t = 1) (hs : G.Side X Y s) (ht : G.Side Y X t) (hh : G.Side X Y h) :
    G.dist s h ≤ G.dist t h := by
  have hne := not_badConfig hXY hstep s t h
  have htri : G.dist s h ≤ G.dist s t + G.dist t h := G.dist_triangle s t h
  unfold BadConfig at hne
  push_neg at hne
  have := hne hst hs ht hh
  omega

/-- **The halfspaces of an edge are convex**: a vertex lying on a geodesic between two vertices
of the `X`-side lies on the `X`-side. -/
theorem side_convex {X Y : Vx} (hXY : G.dist X Y = 1) (hstep : G.HasSteps) :
    ∀ a b c : Vx, G.Side X Y a → G.Side X Y b → G.dist a c + G.dist c b = G.dist a b →
      G.Side X Y c := by
  intro a b c
  induction hn : G.dist a b using Nat.strong_induction_on generalizing a b c with
  | _ n ih =>
  subst hn
  intro ha hb hbetween
  by_cases hac : a = c
  · exact hac ▸ ha
  obtain ⟨a', ha'1, ha'2⟩ := hstep a c hac
  have h1 : G.dist a' b ≤ G.dist a' c + G.dist c b := G.dist_triangle a' c b
  have h2 : G.dist a b ≤ G.dist a a' + G.dist a' b := G.dist_triangle a a' b
  have hlt : G.dist a' b + 1 = G.dist a b := by omega
  have hbet' : G.dist a' c + G.dist c b = G.dist a' b := by omega
  rcases side_dichotomy hXY a' with hside | hside
  · exact ih (G.dist a' b) (by omega) a' b c rfl hside hb hbet'
  · exfalso
    have := side_dist_le hXY hstep ha'1 ha hside hb
    omega

/-- **Distinct vertices are separated by the wall of some edge.** -/
theorem exists_separating_edge (hstep : G.HasSteps) {u v : Vx} (huv : u ≠ v) :
    ∃ X Y : Vx, G.dist X Y = 1 ∧ G.Side X Y u ∧ G.Side Y X v := by
  obtain ⟨c, hc1, hc2⟩ := hstep u v huv
  refine ⟨u, c, hc1, ?_, ?_⟩
  · show G.dist u c = G.dist u u + 1
    rw [G.dist_self u, hc1]
  · show G.dist v u = G.dist v c + 1
    rw [G.dist_comm v u, G.dist_comm v c]
    omega

end MedianGraph

namespace MedianSimpleGraph

variable {Vx : Type u} (M : MedianSimpleGraph Vx)

open SimpleGraph

/-- In a connected graph one can always step towards another vertex along an edge. -/
theorem hasSteps : (M.toMedianGraph).HasSteps := by
  intro a b hab
  have hreach : M.G.Reachable a b := M.conn.preconnected a b
  obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
  cases p with
  | nil => exact absurd rfl hab
  | @cons _ y _ hadj q =>
      refine ⟨y, SimpleGraph.dist_eq_one_iff_adj.mpr hadj, ?_⟩
      have h1 : M.G.dist y b ≤ q.length := SimpleGraph.dist_le q
      have h2 : M.G.dist a b ≤ M.G.dist a y + M.G.dist y b := M.conn.dist_triangle
      have h3 : M.G.dist a y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
      simp only [SimpleGraph.Walk.length_cons] at hp
      show M.G.dist y b + 1 = M.G.dist a b
      omega

/-- **The halfspaces of an edge of a median graph are convex.** -/
theorem side_convex {X Y : Vx} (hXY : M.G.Adj X Y) (a b c : Vx)
    (ha : (M.toMedianGraph).Side X Y a) (hb : (M.toMedianGraph).Side X Y b)
    (hbetween : M.G.dist a c + M.G.dist c b = M.G.dist a b) :
    (M.toMedianGraph).Side X Y c :=
  MedianGraph.side_convex (SimpleGraph.dist_eq_one_iff_adj.mpr hXY) M.hasSteps a b c ha hb
    hbetween

/-- **Distinct vertices of a median graph are separated by the wall of some edge.** -/
theorem exists_separating_edge {u v : Vx} (huv : u ≠ v) :
    ∃ X Y : Vx, M.G.Adj X Y ∧ (M.toMedianGraph).Side X Y u ∧ (M.toMedianGraph).Side Y X v := by
  obtain ⟨X, Y, hXY, hu, hv⟩ := MedianGraph.exists_separating_edge M.hasSteps huv
  exact ⟨X, Y, SimpleGraph.dist_eq_one_iff_adj.mp hXY, hu, hv⟩

end MedianSimpleGraph

end FiniteChains
