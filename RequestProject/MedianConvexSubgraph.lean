import RequestProject.MedianGate
import RequestProject.MedianSimplyConnected

/-!
# Convex subcomplexes are isometrically embedded and simply connected

`RequestProject/MedianGate.lean` shows that a nonempty convex subset `S` of a median graph is a
gated retract.  Here the same subset is studied as a *subgraph*: the induced graph on `S`.

* `FiniteChains.MedianSimpleGraph.exists_induced_walk` — between two vertices of a convex set
  there is a geodesic of the ambient graph lying entirely inside `S`;
* `FiniteChains.MedianSimpleGraph.induce_dist_eq` — hence `S` is **isometrically embedded**: the
  distance in the induced graph is the ambient distance;
* `FiniteChains.MedianSimpleGraph.convexSub` — the induced graph on a nonempty convex set is
  again a median graph of dimension at most three;
* `FiniteChains.MedianSimpleGraph.convexSub_simplyConnected` — therefore its square complex is
  **simply connected**, and `FiniteChains.MedianSimpleGraph.convexSub_ker_d₂_eq_range_d₃` — its
  second homology vanishes.

Together with the gate retraction of `MedianGate.lean` this is the combinatorial content of
step 1 of the generation lemma (property (B2)): a convex subcomplex of a CAT(0) cube complex is
a retract, is isometrically embedded and is itself CAT(0).
-/

namespace FiniteChains

universe u

namespace MedianSimpleGraph

variable {Vx : Type u} (M : MedianSimpleGraph Vx) {S : Set Vx}

/-- **Geodesics between points of a convex set stay inside it.** -/
theorem exists_induced_walk (hS : (M.toMedianGraph).IsConvex S) :
    ∀ (n : ℕ) (a b : S), M.G.dist a.1 b.1 = n →
      ∃ p : (SimpleGraph.induce S M.G).Walk a b, p.length = n := by
  intro n
  induction n with
  | zero =>
      intro a b hab
      have : a.1 = b.1 := (M.toMedianGraph).eq_of_dist_eq_zero hab
      cases Subtype.ext this
      exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ n ih =>
      intro a b hab
      have hne : a.1 ≠ b.1 := by
        intro h
        rw [h] at hab
        simp [SimpleGraph.dist_self] at hab
      obtain ⟨c, hc1, hc2⟩ := M.hasSteps a.1 b.1 hne
      have hcS : c ∈ S := by
        refine hS a.1 a.2 b.1 b.2 c ?_
        have : M.toMedianGraph.dist a.1 b.1 = n + 1 := hab
        omega
      have hadj : M.G.Adj a.1 c := M.dist_eq_one_iff_adj.1 hc1
      have hc2' : M.G.dist c b.1 + 1 = M.G.dist a.1 b.1 := hc2
      have hcb : M.G.dist c b.1 = n := by omega
      obtain ⟨q, hq⟩ := ih ⟨c, hcS⟩ b hcb
      have hadj' : (SimpleGraph.induce S M.G).Adj a ⟨c, hcS⟩ := hadj
      exact ⟨SimpleGraph.Walk.cons hadj' q, by simp [hq]⟩

/-- The induced graph on a convex set is connected, provided the set is nonempty. -/
theorem induce_connected (hS : (M.toMedianGraph).IsConvex S) (hne : S.Nonempty) :
    (SimpleGraph.induce S M.G).Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨fun a b => ?_, ⟨⟨hne.choose, hne.choose_spec⟩⟩⟩
  obtain ⟨p, _⟩ := M.exists_induced_walk hS (M.G.dist a.1 b.1) a b rfl
  exact ⟨p⟩

/-- **A convex set is isometrically embedded**: the distance inside the induced graph agrees
with the ambient distance. -/
theorem induce_dist_eq (hS : (M.toMedianGraph).IsConvex S) (a b : S) :
    (SimpleGraph.induce S M.G).dist a b = M.G.dist a.1 b.1 := by
  refine le_antisymm ?_ ?_
  · obtain ⟨p, hp⟩ := M.exists_induced_walk hS (M.G.dist a.1 b.1) a b rfl
    exact hp ▸ SimpleGraph.dist_le p
  · obtain ⟨p, _⟩ := M.exists_induced_walk hS (M.G.dist a.1 b.1) a b rfl
    obtain ⟨q, hq⟩ := (SimpleGraph.Reachable.exists_walk_length_eq_dist ⟨p⟩)
    have hmap : M.G.dist a.1 b.1 ≤ (q.map (SimpleGraph.Embedding.induce S).toHom).length :=
      SimpleGraph.dist_le _
    rw [SimpleGraph.Walk.length_map, hq] at hmap
    exact hmap

/-- **A nonempty convex subgraph of a median graph is a median graph.** -/
noncomputable def convexSub (hS : (M.toMedianGraph).IsConvex S) (hne : S.Nonempty) :
    MedianSimpleGraph S where
  G := SimpleGraph.induce S M.G
  conn := M.induce_connected hS hne
  base := ⟨(M.toMedianGraph).gate hS hne M.base, MedianGraph.gate_mem hS hne M.base⟩
  med a b c := ⟨M.med a.1 b.1 c.1, hS.med_mem c.1 a.2 b.2⟩
  med_ab a b c := by
    simp only [M.induce_dist_eq hS]
    exact M.med_ab a.1 b.1 c.1
  med_bc a b c := by
    simp only [M.induce_dist_eq hS]
    exact M.med_bc a.1 b.1 c.1
  med_ac a b c := by
    simp only [M.induce_dist_eq hS]
    exact M.med_ac a.1 b.1 c.1
  med_unique a b c z h1 h2 h3 := by
    simp only [M.induce_dist_eq hS] at h1 h2 h3
    exact Subtype.ext (M.med_unique a.1 b.1 c.1 z.1 h1 h2 h3)
  dim_le := by
    classical
    intro w s hs
    have hbase : ∀ a : Vx, a ∈ S →
        M.G.dist M.base a
          = M.G.dist M.base ((M.toMedianGraph).gate hS hne M.base)
            + M.G.dist ((M.toMedianGraph).gate hS hne M.base) a :=
      fun a ha => (MedianGraph.gate_spec hS hne M.base ha).symm
    have himg : ∀ a ∈ s.image (Subtype.val), M.G.Adj a w.1 ∧ M.G.dist M.base a + 1
        = M.G.dist M.base w.1 := by
      intro a ha
      rcases Finset.mem_image.1 ha with ⟨b, hb, rfl⟩
      obtain ⟨h1, h2⟩ := hs b hb
      have h2' : M.G.dist ((M.toMedianGraph).gate hS hne M.base) b.1 + 1
          = M.G.dist ((M.toMedianGraph).gate hS hne M.base) w.1 := by
        rw [M.induce_dist_eq hS, M.induce_dist_eq hS] at h2
        exact h2
      refine ⟨h1, ?_⟩
      have hb' := hbase b.1 b.2
      have hw' := hbase w.1 w.2
      omega
    have hcard := M.dim_le w.1 (s.image (Subtype.val)) himg
    rwa [Finset.card_image_of_injective _ Subtype.val_injective] at hcard

/-- **The square complex of a convex subcomplex is simply connected.** -/
theorem convexSub_simplyConnected (hS : (M.toMedianGraph).IsConvex S) (hne : S.Nonempty) :
    SquareComplex.SimplyConnected (M.convexSub hS hne).toSquareComplex :=
  (M.convexSub hS hne).toSquareComplex_simplyConnected

/-- **The second homology of a convex subcomplex vanishes.** -/
theorem convexSub_ker_d₂_eq_range_d₃ (hS : (M.toMedianGraph).IsConvex S) (hne : S.Nonempty)
    [LinearOrder S] (z : ((M.convexSub hS hne).toDescCubeStr).SqC →₀ ℤ)
    (hz : (M.convexSub hS hne).toDescCubeStr.d₂ z = 0) :
    ∃ y : ((M.convexSub hS hne).toDescCubeStr).CbC →₀ ℤ,
      (M.convexSub hS hne).toDescCubeStr.d₃ y = z :=
  (M.convexSub hS hne).exists_d₃_eq z hz

end MedianSimpleGraph

end FiniteChains
