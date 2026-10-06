import RequestProject.SquareComplexMedianCriterion
import RequestProject.MedianSimplyConnected

/-!
# Uniqueness of medians from the descending–square property

This file reduces the unproved half of Gromov's criterion to a single geometric input.  So far
the project derived a median one-skeleton from two separate metric hypotheses on the one-skeleton
(`FiniteChains.QuadrangleCondition` and `FiniteChains.SquareComplex.HalfspaceConvex`, see
`RequestProject/SquareComplexMedianCriterion.lean`).  Here the conclusion itself — a median
one-skeleton — is derived from the single combinatorial property

> `FiniteChains.SquareComplex.DescendingSquares`: for every base vertex `x`, two distinct
> neighbours `u ≠ v` of a vertex `q` which are one step closer to `x` than `q` is span a
> **two-cell** `S.sq u q v w` of the complex whose fourth vertex `w` is one step closer still.

together with the elementary link hypothesis

> `FiniteChains.SquareComplex.CornerUnique`: a corner `a, b, c` lies on at most one two-cell
> (the link of a vertex is a simplicial graph — part of the flag condition),

and metric bipartiteness, which for a simply connected complex is free
(`FiniteChains.SquareComplex.metricBipartite_of_simplyConnected`).

## Main results

* `FiniteChains.SquareComplex.quadrangleCondition_of_descendingSquares` — the descending-square
  property implies the quadrangle condition, hence (with bipartiteness) the existence of medians;
* `FiniteChains.SquareComplex.median_unique_of_descendingSquares` — **uniqueness of medians**:
  no curvature input beyond `DescendingSquares` and `CornerUnique` is used, and in particular no
  hyperplane, halfspace or separation argument, and no local finiteness;
* `FiniteChains.SquareComplex.medianSimpleGraph_of_descendingSquares` — the one-skeleton is a
  median graph.

## The proof of uniqueness

Let `z ≠ z'` be two medians of `a, b, c` and put `F y = d(a,y) + d(b,y) + d(c,y)`.  Doubling the
three median equations shows `2 * F z = d(a,b) + d(b,c) + d(a,c) = 2 * F z'`, and the triangle
inequality shows that this common value is the *minimum* of `F`.  Take a shortest path from `z`
to `z'` minimising the total weight `∑ᵢ F (γ i)` (a natural number, so a minimiser exists).  Along
an edge each of the three distances changes by exactly one, so `F` changes by an odd number; since
`F` is minimal at both ends, it goes up at the start and down at the end, so it attains an interior
strict maximum at some vertex `q = γ i` with neighbours `u = γ (i-1)`, `v = γ (i+1)` on the path.

At such a vertex at least two of `a, b, c` are closer to `u` than to `q` and at least two are
closer to `v` than to `q`; two two-element subsets of a three-element set meet, so some `x` among
`a, b, c` has *both* `u` and `v` closer to it than `q`.  The descending-square property then
produces the two-cell `S.sq u q v w` with `d(x,w) = d(x,q) - 2`, and `w` is adjacent to `u` and to
`v`, so each of the other two points is at most as far from `w` as from `q` as soon as it descends
on one of the two sides.  The only remaining case is that one of the three ascends on both sides;
then the other two both descend on both sides, and `CornerUnique` says that the two-cell they
produce is the same one, so that vertex is two steps closer for *two* of the three points.  In
every case `F w + 2 ≤ F q`, and replacing `γ i` by `w` gives a shortest path of strictly smaller
total weight — contradicting minimality.  Hence `z = z'`.

## What is *not* proved here

`DescendingSquares` itself is the remaining geometric input of Gromov's criterion; it is exactly
the statement that has to be extracted from simple connectivity and the flag link condition, and
it is not proved here.  Note also that it is a statement about the existence of a *two-cell*, so
it is a different condition from the two metric hypotheses it replaces, not a weakening of them;
see the discussion in `VERIFICATION.md`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

universe u

open SimpleGraph

namespace SquareComplex

variable {Vx : Type u} {S : SquareComplex Vx} {G : SimpleGraph Vx}

/-- **The link is a simplicial graph**: a corner `a, b, c` (a path of two edges) lies on at most
one two-cell.  This is the part of the flag condition which says that two edges at a vertex span
at most one square. -/
def CornerUnique (S : SquareComplex Vx) : Prop :=
  ∀ {a b c d d' : Vx}, S.sq a b c d → S.sq a b c d' → d = d'

/-- **The descending-square property.**  For every base vertex `x`, two distinct neighbours of a
vertex `q`, both one step closer to `x` than `q` is, span a two-cell of the complex whose fourth
vertex is two steps closer to `x` than `q` is.  This is the combinatorial form of nonpositive
curvature used below; it strengthens `FiniteChains.QuadrangleCondition` by asking for an actual
two-cell. -/
def DescendingSquares (S : SquareComplex Vx) (G : SimpleGraph Vx) : Prop :=
  ∀ x q u v : Vx, G.Adj u q → G.Adj v q → u ≠ v →
    G.dist x u + 1 = G.dist x q → G.dist x v + 1 = G.dist x q →
      ∃ w : Vx, S.sq u q v w ∧ G.dist x w + 2 = G.dist x q

/-- The descending-square property implies the quadrangle condition. -/
theorem quadrangleCondition_of_descendingSquares (hadj : ∀ a b : Vx, S.adj a b ↔ G.Adj a b)
    (hsq : DescendingSquares S G) : QuadrangleCondition G := by
  intro x q u v hu hv huv hdu hdv
  obtain ⟨w, hw, hdw⟩ := hsq x q u v hu hv huv hdu hdv
  obtain ⟨-, -, hvw, hwu⟩ := S.sq_adj hw
  exact ⟨w, (hadj w u).1 hwu, (hadj w v).1 (S.adj_symm hvw), hdw⟩

/-! ### Elementary metric facts -/

/-- Along an edge, the distance to a vertex changes by exactly one. -/
theorem dist_edge_cases (hconn : G.Connected) (hbip : MetricBipartite G) {x u v : Vx}
    (h : G.Adj u v) : G.dist x v + 1 = G.dist x u ∨ G.dist x u + 1 = G.dist x v := by
  have h1 : G.dist x v ≤ G.dist x u + 1 := by
    have := hconn.dist_triangle (u := x) (v := u) (w := v)
    have h2 : G.dist u v ≤ 1 := by simpa using SimpleGraph.dist_le h.toWalk
    omega
  have h2 : G.dist x u ≤ G.dist x v + 1 := by
    have := hconn.dist_triangle (u := x) (v := v) (w := u)
    have h3 : G.dist v u ≤ 1 := by simpa using SimpleGraph.dist_le h.symm.toWalk
    omega
  have := hbip x u v h
  omega

/-- A vertex adjacent to `u` is at most one step further from any vertex than `u` is. -/
theorem dist_le_succ_of_adj (hconn : G.Connected) {x u w : Vx} (h : G.Adj u w) :
    G.dist x w ≤ G.dist x u + 1 := by
  have := hconn.dist_triangle (u := x) (v := u) (w := w)
  have h2 : G.dist u w ≤ 1 := by simpa using SimpleGraph.dist_le h.toWalk
  omega

/-! ### The flattening step -/

/-- **The flattening step.**  If `u` and `v` are distinct neighbours of `q` and each of three
points `p₁, p₂, p₃` is, on at least one of the two sides, closer to that side than to `q`, with
`p₁` closer on both sides, then the two-cell spanned by `u, q, v` has a fourth vertex whose total
distance to the three points is smaller by at least two.  The hypotheses `h2`, `h3` encode the
alternative that one of the two other points ascends on both sides, in which case the remaining
point descends on both sides. -/
theorem flatten_aux (hadj : ∀ a b : Vx, S.adj a b ↔ G.Adj a b) (hcorner : S.CornerUnique)
    (hsq : DescendingSquares S G) (hconn : G.Connected)
    {u q v : Vx} (hu : G.Adj u q) (hv : G.Adj v q) (huv : u ≠ v) {p₁ p₂ p₃ : Vx}
    (h1L : G.dist p₁ u + 1 = G.dist p₁ q) (h1R : G.dist p₁ v + 1 = G.dist p₁ q)
    (h2 : (G.dist p₂ u + 1 = G.dist p₂ q ∨ G.dist p₂ v + 1 = G.dist p₂ q) ∨
          (G.dist p₃ u + 1 = G.dist p₃ q ∧ G.dist p₃ v + 1 = G.dist p₃ q))
    (h3 : (G.dist p₃ u + 1 = G.dist p₃ q ∨ G.dist p₃ v + 1 = G.dist p₃ q) ∨
          (G.dist p₂ u + 1 = G.dist p₂ q ∧ G.dist p₂ v + 1 = G.dist p₂ q)) :
    ∃ w : Vx, S.sq u q v w ∧
      G.dist p₁ w + G.dist p₂ w + G.dist p₃ w + 2 ≤ G.dist p₁ q + G.dist p₂ q + G.dist p₃ q := by
  obtain ⟨w, hw, hd₁⟩ := hsq p₁ q u v hu hv huv h1L h1R
  -- the two sides of the two-cell at `w`
  have hwu : G.Adj u w := by
    obtain ⟨-, -, -, h⟩ := S.sq_adj hw
    exact (hadj u w).1 (S.adj_symm h)
  have hwv : G.Adj v w := (hadj v w).1 (S.sq_adj hw).2.2.1
  -- a point descending on one of the two sides is not further from `w` than from `q`
  have hbound : ∀ y : Vx, (G.dist y u + 1 = G.dist y q ∨ G.dist y v + 1 = G.dist y q) →
      G.dist y w ≤ G.dist y q := by
    intro y hy
    rcases hy with hy | hy
    · have := dist_le_succ_of_adj hconn (x := y) hwu
      omega
    · have := dist_le_succ_of_adj hconn (x := y) hwv
      omega
  -- any point is at most two further from `w` than from `q`
  have hbound2 : ∀ y : Vx, G.dist y w ≤ G.dist y q + 2 := by
    intro y
    have h1 := dist_le_succ_of_adj hconn (x := y) hwu
    have h2 := dist_le_succ_of_adj hconn (x := y) (hu.symm)
    omega
  by_cases hb : G.dist p₂ u + 1 = G.dist p₂ q ∨ G.dist p₂ v + 1 = G.dist p₂ q
  · by_cases hc : G.dist p₃ u + 1 = G.dist p₃ q ∨ G.dist p₃ v + 1 = G.dist p₃ q
    · exact ⟨w, hw, by have := hbound _ hb; have := hbound _ hc; omega⟩
    · obtain ⟨hbL, hbR⟩ := h3.resolve_left hc
      obtain ⟨w₂, hw₂, hd₂⟩ := hsq p₂ q u v hu hv huv hbL hbR
      have hww : w = w₂ := hcorner hw hw₂
      subst hww
      exact ⟨w, hw, by have := hbound2 p₃; omega⟩
  · obtain ⟨hcL, hcR⟩ := h2.resolve_left hb
    obtain ⟨w₃, hw₃, hd₃⟩ := hsq p₃ q u v hu hv huv hcL hcR
    have hww : w = w₃ := hcorner hw hw₃
    subst hww
    exact ⟨w, hw, by have := hbound2 p₂; omega⟩

/-! ### Uniqueness of medians -/

/-- **Uniqueness of medians from the descending-square property.**  In a connected square complex
whose one-skeleton is metrically bipartite, whose corners carry at most one two-cell and which has
the descending-square property, a triple of vertices has at most one median.  No hyperplane,
separation or convexity input is used, and no finiteness of links. -/
theorem median_unique_of_descendingSquares (hadj : ∀ a b : Vx, S.adj a b ↔ G.Adj a b)
    (hconn : G.Connected) (hbip : MetricBipartite G) (hcorner : S.CornerUnique)
    (hsq : DescendingSquares S G) {a b c z z' : Vx}
    (hz : IsMedianOf G a b c z) (hz' : IsMedianOf G a b c z') : z = z' := by
  classical
  by_contra hne
  -- the weight function, minimal exactly at the medians
  let F : Vx → ℕ := fun y => G.dist a y + G.dist b y + G.dist c y
  have hFval : ∀ y : Vx, F y = G.dist a y + G.dist b y + G.dist c y := fun _ => rfl
  have hmin : ∀ y : Vx, F z ≤ F y := by
    intro y
    obtain ⟨e1, e2, e3⟩ := hz
    have c1 : G.dist z b = G.dist b z := SimpleGraph.dist_comm
    have c2 : G.dist z c = G.dist c z := SimpleGraph.dist_comm
    have t1 : G.dist a b ≤ G.dist a y + G.dist y b := hconn.dist_triangle
    have t2 : G.dist b c ≤ G.dist b y + G.dist y c := hconn.dist_triangle
    have t3 : G.dist a c ≤ G.dist a y + G.dist y c := hconn.dist_triangle
    have c3 : G.dist y b = G.dist b y := SimpleGraph.dist_comm
    have c4 : G.dist y c = G.dist c y := SimpleGraph.dist_comm
    simp only [hFval]
    omega
  have hFz' : F z' = F z := by
    obtain ⟨e1, e2, e3⟩ := hz
    obtain ⟨f1, f2, f3⟩ := hz'
    have c1 : G.dist z b = G.dist b z := SimpleGraph.dist_comm
    have c2 : G.dist z c = G.dist c z := SimpleGraph.dist_comm
    have c3 : G.dist z' b = G.dist b z' := SimpleGraph.dist_comm
    have c4 : G.dist z' c = G.dist c z' := SimpleGraph.dist_comm
    simp only [hFval]
    omega
  -- adjacent vertices have different weights
  have hFne : ∀ {x y : Vx}, G.Adj x y → F x ≠ F y := by
    intro x y hxy
    have ha := dist_edge_cases hconn hbip (x := a) hxy
    have hb := dist_edge_cases hconn hbip (x := b) hxy
    have hc := dist_edge_cases hconn hbip (x := c) hxy
    simp only [hFval]
    omega
  set n := G.dist z z' with hndef
  have hzz : G.dist z z' = n := hndef.symm
  have hn0 : n ≠ 0 := fun h => hne (hconn.dist_eq_zero_iff.mp (by rw [hzz]; exact h))
  -- a shortest path from `z` to `z'` of minimal total weight
  obtain ⟨γ, hγ0, hγn, hγadj, hγmin⟩ :
      ∃ γ : ℕ → Vx, γ 0 = z ∧ γ n = z' ∧ (∀ i, i < n → G.Adj (γ i) (γ (i + 1))) ∧
        ∀ δ : ℕ → Vx, δ 0 = z → δ n = z' → (∀ i, i < n → G.Adj (δ i) (δ (i + 1))) →
          (∑ i ∈ Finset.range (n + 1), F (γ i)) ≤ ∑ i ∈ Finset.range (n + 1), F (δ i) := by
    set T : Set ℕ := {m | ∃ δ : ℕ → Vx, (δ 0 = z ∧ δ n = z' ∧ ∀ i, i < n → G.Adj (δ i) (δ (i + 1)))
      ∧ (∑ i ∈ Finset.range (n + 1), F (δ i)) = m} with hT
    have hTne : T.Nonempty := by
      obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist z z'
      have hlen : p.length = n := by rw [hp, hzz]
      refine ⟨_, p.getVert, ⟨by simp, ?_, ?_⟩, rfl⟩
      · rw [← hlen]; exact p.getVert_length
      · intro i hi; exact p.adj_getVert_succ (by omega)
    obtain ⟨γ, hγ, hγsum⟩ := Nat.sInf_mem hTne
    refine ⟨γ, hγ.1, hγ.2.1, hγ.2.2, ?_⟩
    intro δ h0 hn' hadjδ
    have : (∑ i ∈ Finset.range (n + 1), F (δ i)) ∈ T := ⟨δ, ⟨h0, hn', hadjδ⟩, rfl⟩
    rw [hγsum]
    exact Nat.sInf_le this
  -- distances along the path
  have hstep : ∀ (k i : ℕ), i + k ≤ n → G.dist (γ i) (γ (i + k)) ≤ k := by
    intro k
    induction k with
    | zero => intro i _; simp
    | succ k ih =>
        intro i hik
        have h1 : G.Adj (γ i) (γ (i + 1)) := hγadj i (by omega)
        have h2 : G.dist (γ (i + 1)) (γ (i + 1 + k)) ≤ k := ih (i + 1) (by omega)
        have h3 : G.dist (γ i) (γ (i + 1)) ≤ 1 := by simpa using SimpleGraph.dist_le h1.toWalk
        have h4 := hconn.dist_triangle (u := γ i) (v := γ (i + 1)) (w := γ (i + 1 + k))
        have hidx : i + (k + 1) = i + 1 + k := by omega
        rw [hidx]
        omega
  have hdz : ∀ i, i ≤ n → G.dist z (γ i) = i := by
    intro i hi
    have h1 : G.dist z (γ i) ≤ i := by
      have := hstep i 0 (by omega)
      simpa [hγ0] using this
    have h2 : G.dist (γ i) z' ≤ n - i := by
      have := hstep (n - i) i (by omega)
      have hni : i + (n - i) = n := by omega
      rw [hni, hγn] at this
      exact this
    have h3 := hconn.dist_triangle (u := z) (v := γ i) (w := z')
    omega
  -- an interior vertex of maximal weight
  obtain ⟨i₀, hi₀mem, hi₀max⟩ :=
    Finset.exists_max_image (Finset.range (n + 1)) (fun i => F (γ i)) ⟨0, by simp⟩
  have hi₀le : i₀ ≤ n := by
    have := Finset.mem_range.mp hi₀mem
    omega
  have hlt1 : F (γ 0) < F (γ 1) := by
    have h1 := hFne (hγadj 0 (by omega))
    norm_num at h1
    have h2 := hmin (γ 1)
    rw [hγ0] at h1 ⊢
    omega
  have hltn : F (γ n) < F (γ (n - 1)) := by
    have hadjn : G.Adj (γ (n - 1)) (γ (n - 1 + 1)) := hγadj (n - 1) (by omega)
    have hidx : n - 1 + 1 = n := by omega
    rw [hidx] at hadjn
    have h1 := hFne hadjn
    have h2 := hmin (γ (n - 1))
    rw [hγn, hFz']
    rw [hγn, hFz'] at h1
    omega
  have hi0 : i₀ ≠ 0 := by
    intro h
    have := hi₀max 1 (by simp; omega)
    rw [h] at this
    omega
  have hin : i₀ ≠ n := by
    intro h
    have := hi₀max (n - 1) (by simp)
    rw [h] at this
    omega
  -- the peak and its two neighbours on the path
  have hi₀pos : 1 ≤ i₀ := by omega
  have hi₀lt : i₀ < n := by omega
  have hidx1 : i₀ - 1 + 1 = i₀ := by omega
  have hu : G.Adj (γ (i₀ - 1)) (γ i₀) := by
    have := hγadj (i₀ - 1) (by omega)
    rwa [hidx1] at this
  have hv : G.Adj (γ (i₀ + 1)) (γ i₀) := (hγadj i₀ hi₀lt).symm
  have huv : γ (i₀ - 1) ≠ γ (i₀ + 1) := by
    intro h
    have e1 := hdz (i₀ - 1) (by omega)
    have e2 := hdz (i₀ + 1) (by omega)
    rw [h] at e1
    omega
  have hFu : F (γ (i₀ - 1)) < F (γ i₀) := by
    have h1 := hi₀max (i₀ - 1) (by simp; omega)
    have h2 := hFne hu
    omega
  have hFv : F (γ (i₀ + 1)) < F (γ i₀) := by
    have h1 := hi₀max (i₀ + 1) (by simp; omega)
    have h2 := hFne hv
    omega
  -- at the peak, some one of `a, b, c` descends on both sides
  have hau := dist_edge_cases hconn hbip (x := a) hu
  have hbu := dist_edge_cases hconn hbip (x := b) hu
  have hcu := dist_edge_cases hconn hbip (x := c) hu
  have hav := dist_edge_cases hconn hbip (x := a) hv
  have hbv := dist_edge_cases hconn hbip (x := b) hv
  have hcv := dist_edge_cases hconn hbip (x := c) hv
  simp only [hFval] at hFu hFv
  -- the flattened vertex
  obtain ⟨w, hwsq, hwle⟩ : ∃ w : Vx, S.sq (γ (i₀ - 1)) (γ i₀) (γ (i₀ + 1)) w ∧
      F w + 2 ≤ F (γ i₀) := by
    simp only [hFval]
    by_cases hpa : G.dist a (γ (i₀ - 1)) + 1 = G.dist a (γ i₀) ∧
        G.dist a (γ (i₀ + 1)) + 1 = G.dist a (γ i₀)
    · obtain ⟨w, hw, hle⟩ :=
        flatten_aux hadj hcorner hsq hconn hu hv huv (p₁ := a) (p₂ := b) (p₃ := c)
          hpa.1 hpa.2 (by omega) (by omega)
      exact ⟨w, hw, by omega⟩
    · by_cases hpb : G.dist b (γ (i₀ - 1)) + 1 = G.dist b (γ i₀) ∧
          G.dist b (γ (i₀ + 1)) + 1 = G.dist b (γ i₀)
      · obtain ⟨w, hw, hle⟩ :=
          flatten_aux hadj hcorner hsq hconn hu hv huv (p₁ := b) (p₂ := a) (p₃ := c)
            hpb.1 hpb.2 (by omega) (by omega)
        exact ⟨w, hw, by omega⟩
      · have hpc : G.dist c (γ (i₀ - 1)) + 1 = G.dist c (γ i₀) ∧
            G.dist c (γ (i₀ + 1)) + 1 = G.dist c (γ i₀) := by
          constructor <;> omega
        obtain ⟨w, hw, hle⟩ :=
          flatten_aux hadj hcorner hsq hconn hu hv huv (p₁ := c) (p₂ := a) (p₃ := b)
            hpc.1 hpc.2 (by omega) (by omega)
        exact ⟨w, hw, by omega⟩
  -- the flattened path is again a shortest path, of smaller total weight
  have hwu : G.Adj (γ (i₀ - 1)) w := by
    obtain ⟨-, -, -, h⟩ := S.sq_adj hwsq
    exact ((hadj _ _).1 h).symm
  have hwv : G.Adj w (γ (i₀ + 1)) := ((hadj _ _).1 (S.sq_adj hwsq).2.2.1).symm
  set δ : ℕ → Vx := Function.update γ i₀ w with hδdef
  have hδne : ∀ i, i ≠ i₀ → δ i = γ i := fun i h => Function.update_of_ne h _ _
  have hδeq : δ i₀ = w := Function.update_self _ _ _
  have hδ0 : δ 0 = z := by rw [hδne 0 (by omega), hγ0]
  have hδn : δ n = z' := by rw [hδne n (by omega), hγn]
  have hδadj : ∀ i, i < n → G.Adj (δ i) (δ (i + 1)) := by
    intro i hi
    by_cases h1 : i = i₀
    · subst h1
      rw [hδeq, hδne (i + 1) (by omega)]
      exact hwv
    · by_cases h2 : i + 1 = i₀
      · have hi1 : i = i₀ - 1 := by omega
        subst hi1
        rw [hδne _ (by omega), h2, hδeq]
        exact hwu
      · rw [hδne i h1, hδne (i + 1) h2]
        exact hγadj i hi
  have hsum : (∑ i ∈ Finset.range (n + 1), F (δ i)) + 2 ≤
      ∑ i ∈ Finset.range (n + 1), F (γ i) := by
    have hmem : i₀ ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have e1 : (∑ i ∈ Finset.range (n + 1), F (γ i)) =
        (∑ i ∈ Finset.range (n + 1) \ {i₀}, F (γ i)) + F (γ i₀) :=
      by simpa only [Finset.sdiff_singleton_eq_erase] using
        (Finset.sum_erase_add (Finset.range (n + 1)) (fun i => F (γ i)) hmem).symm
    have e2 : (∑ i ∈ Finset.range (n + 1), F (δ i)) =
        (∑ i ∈ Finset.range (n + 1) \ {i₀}, F (δ i)) + F (δ i₀) :=
      by simpa only [Finset.sdiff_singleton_eq_erase] using
        (Finset.sum_erase_add (Finset.range (n + 1)) (fun i => F (δ i)) hmem).symm
    have e3 : (∑ i ∈ Finset.range (n + 1) \ {i₀}, F (δ i)) =
        ∑ i ∈ Finset.range (n + 1) \ {i₀}, F (γ i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have : i ≠ i₀ := by
        have := Finset.mem_sdiff.mp hi
        simpa using this.2
      rw [hδne i this]
    rw [e1, e2, e3, hδeq]
    omega
  have := hγmin δ hδ0 hδn hδadj
  omega

/-! ### The median one-skeleton -/

/-- **The one-skeleton is a median graph.**  A connected square complex with at most one two-cell
on each corner, metrically bipartite one-skeleton and the descending-square property has a median
one-skeleton: every triple of vertices has exactly one median.  (`hdim` is the dimension bound
carried by `FiniteChains.MedianSimpleGraph`; it is not part of the criterion.) -/
noncomputable def medianSimpleGraph_of_descendingSquares (hadj : ∀ a b : Vx, S.adj a b ↔ G.Adj a b)
    (hconn : G.Connected) (hbip : MetricBipartite G) (hcorner : S.CornerUnique)
    (hsq : DescendingSquares S G) (base : Vx)
    (hdim : ∀ (w : Vx) (s : Finset Vx),
      (∀ a ∈ s, G.Adj a w ∧ G.dist base a + 1 = G.dist base w) → s.card ≤ 3) :
    MedianSimpleGraph Vx := by
  classical
  have hQC : QuadrangleCondition G := quadrangleCondition_of_descendingSquares hadj hsq
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
  exact median_unique_of_descendingSquares hadj hconn hbip hcorner hsq ⟨h1, h2, h3⟩
    (Classical.choose_spec (hex a b c))

/-- **Every triple has a unique median.**  The same statement without the dimension bound. -/
theorem existsUnique_median_of_descendingSquares (hadj : ∀ a b : Vx, S.adj a b ↔ G.Adj a b)
    (hconn : G.Connected) (hbip : MetricBipartite G) (hcorner : S.CornerUnique)
    (hsq : DescendingSquares S G) (a b c : Vx) : ∃! z : Vx, IsMedianOf G a b c z := by
  obtain ⟨z, hz⟩ :=
    exists_median hconn hbip (quadrangleCondition_of_descendingSquares hadj hsq) a b c
  exact ⟨z, hz, fun z' hz' => median_unique_of_descendingSquares hadj hconn hbip hcorner hsq hz' hz⟩

/-- **Gromov's criterion, reduced to the descending-square property.**  A connected, simply
connected square complex with at most one two-cell on each corner and the descending-square
property has a median one-skeleton.  Metric bipartiteness is supplied by simple connectivity, so
the only curvature input left is `DescendingSquares`. -/
theorem existsUnique_median_of_simplyConnected (hadj : ∀ a b : Vx, S.adj a b ↔ G.Adj a b)
    (hSC : S.SimplyConnected) (hconn : G.Connected) (hcorner : S.CornerUnique)
    (hsq : DescendingSquares S G) (a b c : Vx) : ∃! z : Vx, IsMedianOf G a b c z :=
  existsUnique_median_of_descendingSquares hadj hconn
    (metricBipartite_of_simplyConnected hadj hSC hconn) hcorner hsq a b c

end SquareComplex

/-! ### Non-vacuity: median graphs satisfy the hypotheses -/

namespace MedianSimpleGraph

variable {Vx : Type u} (M : MedianSimpleGraph Vx)

/-- **The square complex of a median graph has simplicial links**: a corner lies on at most one
two-cell.  (Two two-cells on one corner would give three common neighbours of two vertices at
distance two, which a median graph does not have.) -/
theorem toSquareComplex_cornerUnique : (M.toSquareComplex).CornerUnique := by
  intro a b c d d' h h'
  obtain ⟨hab, hbc, hcd, hda, hac, hbd⟩ := h
  obtain ⟨-, -, hcd', hd'a, -, hbd'⟩ := h'
  by_contra hdd'
  exact M.no_K23 (M.gdist_two_of_common_neighbour hab (M.G.symm.symm _ _ hbc) hac)
    (M.G.symm.symm _ _ hab) hbc hd'a (M.G.symm.symm _ _ hcd') hda (M.G.symm.symm _ _ hcd)
    hbd' hbd (Ne.symm hdd')

/-- **The square complex of a median graph has the descending-square property**: two distinct
neighbours of `q` closer to `x` span a two-cell whose fourth vertex is closer still.  Together
with `FiniteChains.MedianSimpleGraph.toSquareComplex_cornerUnique` this shows that the hypotheses
of `FiniteChains.SquareComplex.median_unique_of_descendingSquares` are exactly satisfied by median
graphs, so the criterion proved above is not vacuous. -/
theorem toSquareComplex_descendingSquares :
    SquareComplex.DescendingSquares (M.toSquareComplex) M.G := by
  intro x q u v hu hv huv hdu hdv
  obtain ⟨hmu, hmv, hmx, hmq⟩ := M.quadrangle_graph hu (M.G.symm.symm _ _ hv) huv hdu hdv
  exact ⟨M.med u v x, ⟨hu, M.G.symm.symm _ _ hv, hmv, M.G.symm.symm _ _ hmu, huv, Ne.symm hmq⟩, by omega⟩

/-- **The criterion applied to a median graph returns its medians**: every triple of vertices of a
median graph has a unique median, as recovered from
`FiniteChains.SquareComplex.existsUnique_median_of_descendingSquares`. -/
theorem existsUnique_median_of_criterion (a b c : Vx) : ∃! z : Vx, IsMedianOf M.G a b c z :=
  SquareComplex.existsUnique_median_of_descendingSquares (S := M.toSquareComplex)
    (fun _ _ => Iff.rfl) M.conn
    (fun y _ _ hst => M.dist_ne_of_adj (x := y) hst)
    M.toSquareComplex_cornerUnique M.toSquareComplex_descendingSquares a b c

end MedianSimpleGraph

end FiniteChains
