module

public import RequestProject.MedianHalfspaces

@[expose] public section

/-!
# Convex subcomplexes of median graphs are gated retracts

This file proves the combinatorial form of the *radial (geodesic) retraction* onto a convex
subcomplex of a CAT(0) cube complex, which is the remaining geometric input of step 1 of the
generation lemma (property (B2)): the retraction of the cover onto the chosen copy of `X`.

In the median (combinatorial) model the statement is the classical one:

* `FiniteChains.MedianGraph.exists_gate` — a nonempty convex set `S` is **gated**: for every
  vertex `x` there is a vertex `s ∈ S` lying on a geodesic from `x` to every vertex of `S`;
* `FiniteChains.MedianGraph.gate_unique`, `FiniteChains.MedianGraph.gate_spec` — the gate is
  unique, so the **gate map** `FiniteChains.MedianGraph.gate` is well defined;
* `FiniteChains.MedianGraph.gate_eq_self_of_mem` — it is a **retraction**: it is the identity
  on `S`;
* `FiniteChains.MedianGraph.dist_gate_le` — the gate is the (unique) nearest point of `S`;
* `FiniteChains.MedianGraph.gate_nonexpansive` — the retraction is distance non-increasing,
  and `FiniteChains.MedianGraph.gate_adj` — it maps an edge to an edge or to a vertex, that is,
  it is a retraction of the one-skeleton;
* `FiniteChains.MedianGraph.restrict` — a nonempty convex subset is itself a median graph of
  dimension at most three, and hence, by `FiniteChains.MedianGraph.ker_d₂_eq_range_d₃`
  (`FiniteChains.MedianGraph.restrict_ker_d₂_eq_range_d₃`), its own second homology vanishes.

Nothing here is assumed: everything is derived from the axioms of a median graph.  That the
hypotheses are not vacuous is witnessed by the halfspaces of an edge, which are convex
(`FiniteChains.MedianGraph.side_convex`) and therefore gated
(`FiniteChains.MedianGraph.side_isConvex`, `FiniteChains.MedianGraph.exists_gate_side`).
-/

namespace FiniteChains

universe u

namespace MedianGraph

variable {Vx : Type u} (G : MedianGraph Vx)

/-! ### Convexity -/

/-- A set is **convex** when it contains, with any two of its points, every point on a
geodesic between them. -/
def IsConvex (S : Set Vx) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ z : Vx, G.dist a z + G.dist z b = G.dist a b → z ∈ S

variable {G}

/-- A convex set is closed under medians (the third argument may be arbitrary: the median
lies on a geodesic between the first two). -/
theorem IsConvex.med_mem {S : Set Vx} (hS : G.IsConvex S) {a b : Vx} (c : Vx) (ha : a ∈ S)
    (hb : b ∈ S) : G.med a b c ∈ S :=
  hS a ha b hb _ (G.med_ab a b c)

/-! ### Gates -/

/-- `s` is a **gate** of `x` in `S`: it belongs to `S` and lies on a geodesic from `x` to every
point of `S`. -/
def IsGate (G : MedianGraph Vx) (S : Set Vx) (x s : Vx) : Prop :=
  s ∈ S ∧ ∀ t ∈ S, G.dist x s + G.dist s t = G.dist x t

/-- **A nonempty convex set is gated.**  The nearest point of `S` to `x` is a gate: if `t ∈ S`,
then the median of `x`, of the nearest point `s` and of `t` lies in `S` (it is on the geodesic
from `s` to `t`) and on the geodesic from `x` to `s`, hence equals `s` by minimality. -/
theorem exists_gate {S : Set Vx} (hS : G.IsConvex S) (hne : S.Nonempty) (x : Vx) :
    ∃ s, G.IsGate S x s := by
  classical
  have hex : ∃ n, ∃ t ∈ S, G.dist x t = n := ⟨G.dist x hne.choose, hne.choose, hne.choose_spec, rfl⟩
  obtain ⟨s, hsS, hsn⟩ := Nat.find_spec hex
  have hmin : ∀ t ∈ S, G.dist x s ≤ G.dist x t := by
    intro t ht
    have : Nat.find hex ≤ G.dist x t := Nat.find_le ⟨t, ht, rfl⟩
    omega
  refine ⟨s, hsS, fun t ht => ?_⟩
  have hm : G.med x s t ∈ S := hS s hsS t ht _ (G.med_bc x s t)
  have h1 : G.dist x (G.med x s t) + G.dist (G.med x s t) s = G.dist x s := G.med_ab x s t
  have h2 : G.dist x (G.med x s t) + G.dist (G.med x s t) t = G.dist x t := G.med_ac x s t
  have h3 : G.dist x s ≤ G.dist x (G.med x s t) := hmin _ hm
  have h4 : G.dist (G.med x s t) s = 0 := by omega
  have h5 : G.med x s t = s := G.eq_of_dist_eq_zero h4
  rw [h5] at h2
  exact h2

/-- The gate is unique. -/
theorem gate_unique {S : Set Vx} {x s s' : Vx} (h : G.IsGate S x s) (h' : G.IsGate S x s') :
    s = s' := by
  have h1 := h.2 s' h'.1
  have h2 := h'.2 s h.1
  have h3 : G.dist s s' = G.dist s' s := G.dist_comm s s'
  have : G.dist s s' = 0 := by omega
  exact G.eq_of_dist_eq_zero this

variable (G)

/-- The **gate map**, the combinatorial radial retraction onto a nonempty convex set. -/
noncomputable def gate {S : Set Vx} (hS : G.IsConvex S) (hne : S.Nonempty) (x : Vx) : Vx :=
  (exists_gate hS hne x).choose

variable {G}

theorem gate_isGate {S : Set Vx} (hS : G.IsConvex S) (hne : S.Nonempty) (x : Vx) :
    G.IsGate S x (G.gate hS hne x) :=
  (exists_gate hS hne x).choose_spec

theorem gate_mem {S : Set Vx} (hS : G.IsConvex S) (hne : S.Nonempty) (x : Vx) :
    G.gate hS hne x ∈ S := (gate_isGate hS hne x).1

/-- The defining property of the gate: it lies on a geodesic from `x` to every point of `S`. -/
theorem gate_spec {S : Set Vx} (hS : G.IsConvex S) (hne : S.Nonempty) (x : Vx) {t : Vx}
    (ht : t ∈ S) : G.dist x (G.gate hS hne x) + G.dist (G.gate hS hne x) t = G.dist x t :=
  (gate_isGate hS hne x).2 t ht

/-- The gate map is a **retraction**: it fixes `S` pointwise. -/
theorem gate_eq_self_of_mem {S : Set Vx} (hS : G.IsConvex S) (hne : S.Nonempty) {x : Vx}
    (hx : x ∈ S) : G.gate hS hne x = x :=
  gate_unique (gate_isGate hS hne x) ⟨hx, fun t _ => by rw [G.dist_self, Nat.zero_add]⟩

/-- The gate is the nearest point of `S`. -/
theorem dist_gate_le {S : Set Vx} (hS : G.IsConvex S) (hne : S.Nonempty) (x : Vx) {t : Vx}
    (ht : t ∈ S) : G.dist x (G.gate hS hne x) ≤ G.dist x t := by
  have := gate_spec hS hne x ht
  omega

/-- **The retraction does not increase distances.** -/
theorem gate_nonexpansive {S : Set Vx} (hS : G.IsConvex S) (hne : S.Nonempty) (x y : Vx) :
    G.dist (G.gate hS hne x) (G.gate hS hne y) ≤ G.dist x y := by
  have hx := gate_spec hS hne x (gate_mem hS hne y)
  have hy := gate_spec hS hne y (gate_mem hS hne x)
  have hxy : G.dist x (G.gate hS hne y) ≤ G.dist x y + G.dist y (G.gate hS hne y) :=
    G.dist_triangle _ _ _
  have hyx : G.dist y (G.gate hS hne x) ≤ G.dist y x + G.dist x (G.gate hS hne x) :=
    G.dist_triangle _ _ _
  have hsymm : G.dist y x = G.dist x y := G.dist_comm y x
  have hgg : G.dist (G.gate hS hne y) (G.gate hS hne x)
      = G.dist (G.gate hS hne x) (G.gate hS hne y) := G.dist_comm _ _
  omega

/-- The retraction maps an edge to an edge or collapses it: it is a retraction of the
one-skeleton. -/
theorem gate_adj {S : Set Vx} (hS : G.IsConvex S) (hne : S.Nonempty) {x y : Vx}
    (h : G.dist x y = 1) :
    G.gate hS hne x = G.gate hS hne y ∨ G.dist (G.gate hS hne x) (G.gate hS hne y) = 1 := by
  have hle := gate_nonexpansive hS hne x y
  rw [h] at hle
  interval_cases hd : G.dist (G.gate hS hne x) (G.gate hS hne y)
  · exact Or.inl (G.eq_of_dist_eq_zero hd)
  · exact Or.inr rfl

/-! ### A convex subcomplex is again a median graph -/

/-- **A nonempty convex subset of a median graph is a median graph**, with the restricted
distance, the restricted median and the gate of the base vertex as base vertex. -/
noncomputable def restrict {S : Set Vx} (hS : G.IsConvex S) (hne : S.Nonempty) :
    MedianGraph {x : Vx // x ∈ S} where
  dist a b := G.dist a.1 b.1
  base := ⟨G.gate hS hne G.base, gate_mem hS hne G.base⟩
  dist_self a := G.dist_self a.1
  eq_of_dist_eq_zero h := Subtype.ext (G.eq_of_dist_eq_zero h)
  dist_comm a b := G.dist_comm a.1 b.1
  dist_triangle a b c := G.dist_triangle a.1 b.1 c.1
  med a b c := ⟨G.med a.1 b.1 c.1, hS.med_mem c.1 a.2 b.2⟩
  med_ab a b c := G.med_ab a.1 b.1 c.1
  med_bc a b c := G.med_bc a.1 b.1 c.1
  med_ac a b c := G.med_ac a.1 b.1 c.1
  med_unique a b c z h1 h2 h3 := Subtype.ext (G.med_unique a.1 b.1 c.1 z.1 h1 h2 h3)
  dim_le := by
    classical
    intro w s hs
    have hbase : ∀ a : Vx, a ∈ S →
        G.dist G.base a
          = G.dist G.base (G.gate hS hne G.base) + G.dist (G.gate hS hne G.base) a :=
      fun a ha => (gate_spec hS hne G.base ha).symm
    have himg : ∀ a ∈ s.image (Subtype.val), G.dist a w.1 = 1 ∧ G.dist G.base a + 1
        = G.dist G.base w.1 := by
      intro a ha
      rcases Finset.mem_image.1 ha with ⟨b, hb, rfl⟩
      obtain ⟨h1, h2⟩ := hs b hb
      have h2' : G.dist (G.gate hS hne G.base) b.1 + 1
          = G.dist (G.gate hS hne G.base) w.1 := h2
      refine ⟨h1, ?_⟩
      have hb' := hbase b.1 b.2
      have hw' := hbase w.1 w.2
      omega
    have hcard := G.dim_le w.1 (s.image (Subtype.val)) himg
    rwa [Finset.card_image_of_injective _ Subtype.val_injective] at hcard

/-- **The second homology of a convex subcomplex vanishes too**: every two-cycle of the cellular
complex of a nonempty convex subcomplex of a three-dimensional median graph is a boundary. -/
theorem restrict_ker_d₂_eq_range_d₃ {S : Set Vx} (hS : G.IsConvex S) (hne : S.Nonempty)
    [LinearOrder {x : Vx // x ∈ S}] :
    ∀ z : ((restrict hS hne).toDescCubeStr).SqC →₀ ℤ,
      (restrict hS hne).toDescCubeStr.d₂ z = 0 →
        ∃ y : ((restrict hS hne).toDescCubeStr).CbC →₀ ℤ,
          (restrict hS hne).toDescCubeStr.d₃ y = z :=
  fun z hz => (restrict hS hne).exists_d₃_eq z hz

/-! ### Halfspaces are gated -/

/-- The halfspace of an edge is convex. -/
theorem side_isConvex {X Y : Vx} (hXY : G.dist X Y = 1) (hstep : G.HasSteps) :
    G.IsConvex {t : Vx | G.Side X Y t} :=
  fun a ha b hb z h => side_convex hXY hstep a b z ha hb h

/-- The halfspace of an edge is nonempty: it contains the endpoint `X`. -/
theorem side_nonempty {X Y : Vx} (hXY : G.dist X Y = 1) :
    {t : Vx | G.Side X Y t}.Nonempty :=
  ⟨X, by
    have h : G.dist X Y = G.dist X X + 1 := by rw [G.dist_self, Nat.zero_add, hXY]
    exact h⟩

/-- **The halfspaces of an edge of a median graph are gated**, hence are retracts of the whole
graph by the gate map. -/
theorem exists_gate_side {X Y : Vx} (hXY : G.dist X Y = 1) (hstep : G.HasSteps) (x : Vx) :
    ∃ s, G.IsGate {t : Vx | G.Side X Y t} x s :=
  exists_gate (side_isConvex hXY hstep) (side_nonempty hXY) x

end MedianGraph

end FiniteChains
