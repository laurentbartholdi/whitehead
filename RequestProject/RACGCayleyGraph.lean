module

public import RequestProject.RACGMedianGraph
public import RequestProject.MedianGraphMetric
public import RequestProject.MedianSimplyConnected

@[expose] public section

/-!
# The Cayley graph as a simple graph, and its metric

`RequestProject/RACGMedianGraph.lean` produces the median structure for the word metric.  This
file identifies the word metric with the graph metric of the Cayley graph

  `FiniteChains.RACG.cayleyGraph` : vertices are the group elements, and `x` is joined to
  `x * s` for every generator `s`,

and packages the result as a `FiniteChains.MedianSimpleGraph`:

* `FiniteChains.RACG.cayleyGraph_connected` — the Cayley graph is connected;
* `FiniteChains.RACG.cayleyGraph_dist` — its graph distance is the word length of `x⁻¹ y`;
* `FiniteChains.RACG.cayleyMedianSimpleGraph` — **the Cayley graph of a right-angled Coxeter
  group whose commutation graph has no four-element clique is a median graph.**

Combined with `RequestProject/MedianSimplyConnected.lean` (the square complex of a median graph
is simply connected and has flag links) this is Gromov's criterion, in both directions, for the
cube complexes `C(L)` used in the paper.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace RACG

universe u

variable {V : Type u} [DecidableEq V] (A : CommRel V)

theorem clen_gen_eq_one (s : V) : clen A (gen A s) = 1 := by
  have hred : IsRed A.rel [s] := ⟨trivial, by simp [canStart]⟩
  have hg : gen A s = cword A [s] := by simp
  rw [hg, clen_cword A hred]
  simp

/-- The Cayley graph of the right-angled Coxeter group with respect to its generators. -/
def cayleyGraph : SimpleGraph (CayGroup A) where
  Adj x y := ∃ s : V, y = x * gen A s
  symm := ⟨by
    rintro x y ⟨s, rfl⟩
    exact ⟨s, by rw [mul_assoc, gen_mul_gen, mul_one]⟩⟩
  loopless := by
    refine ⟨?_⟩
    rintro x ⟨s, hs⟩
    have hone : gen A s = 1 := by
      have := congrArg (fun z => x⁻¹ * z) hs
      simpa using this.symm
    have h1 := clen_gen_eq_one A s
    rw [hone, clen_one] at h1
    exact absurd h1 (by omega)

theorem cayleyGraph_adj_iff {x y : CayGroup A} :
    (cayleyGraph A).Adj x y ↔ cdist A x y = 1 := by
  constructor
  · rintro ⟨s, rfl⟩
    have hq : x⁻¹ * (x * gen A s) = gen A s := by group
    show clen A (x⁻¹ * (x * gen A s)) = 1
    rw [hq]
    exact clen_gen_eq_one A s
  · intro h
    obtain ⟨s, hs⟩ := (clen_eq_one_iff A).1 h
    refine ⟨s, ?_⟩
    have h2 := congrArg (fun z => x * z) hs
    simpa using h2

/-- A word gives a walk of the same length. -/
theorem exists_walk : ∀ (l : List V) (x y : CayGroup A), x * cword A l = y →
    ∃ w : (cayleyGraph A).Walk x y, w.length = l.length
  | [], x, y, h => by
      have hxy : x = y := by simpa using h
      subst hxy
      exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | a :: t, x, y, h => by
      have hadj : (cayleyGraph A).Adj x (x * gen A a) := ⟨a, rfl⟩
      obtain ⟨w, hw⟩ := exists_walk t (x * gen A a) y (by rw [← h, cword_cons, mul_assoc])
      exact ⟨SimpleGraph.Walk.cons hadj w, by simp [hw]⟩

theorem cayleyGraph_reachable (x y : CayGroup A) : (cayleyGraph A).Reachable x y := by
  obtain ⟨l, -, hl⟩ := exists_cword A (x⁻¹ * y)
  obtain ⟨w, -⟩ := exists_walk A l x y (by rw [hl]; group)
  exact ⟨w⟩

theorem cayleyGraph_connected : (cayleyGraph A).Connected := by
  rw [SimpleGraph.connected_iff]
  exact ⟨cayleyGraph_reachable A, ⟨1⟩⟩

theorem cdist_le_walk_length {x y : CayGroup A} (w : (cayleyGraph A).Walk x y) :
    cdist A x y ≤ w.length := by
  induction w with
  | nil => simp [cdist]
  | @cons u v z hadj p ih =>
      have h1 : cdist A u v = 1 := (cayleyGraph_adj_iff A).1 hadj
      have h2 : cdist A u z ≤ cdist A u v + cdist A v z := cdist_triangle A u v z
      simp only [SimpleGraph.Walk.length_cons]
      omega

/-- **The graph metric of the Cayley graph is the word metric.** -/
theorem cayleyGraph_dist (x y : CayGroup A) : (cayleyGraph A).dist x y = cdist A x y := by
  refine le_antisymm ?_ ?_
  · obtain ⟨l, hl, hlx⟩ := exists_cword A (x⁻¹ * y)
    obtain ⟨w, hw⟩ := exists_walk A l x y (by rw [hlx]; group)
    calc (cayleyGraph A).dist x y ≤ w.length := SimpleGraph.dist_le w
      _ = l.length := hw
      _ = cdist A x y := by rw [← clen_cword A hl, hlx]; rfl
  · obtain ⟨w, hw⟩ := (cayleyGraph_reachable A x y).exists_walk_length_eq_dist
    calc cdist A x y ≤ w.length := cdist_le_walk_length A w
      _ = (cayleyGraph A).dist x y := hw

/-- **The Cayley graph of a right-angled Coxeter group is a median graph** (in the sense of
graphs with their graph metric), provided the commutation graph has no clique with four
vertices. -/
noncomputable def cayleyMedianSimpleGraph
    (hdim : ∀ t : Finset V, (∀ s ∈ t, ∀ r ∈ t, s ≠ r → A.rel s r) → t.card ≤ 3) :
    MedianSimpleGraph (CayGroup A) where
  G := cayleyGraph A
  conn := cayleyGraph_connected A
  base := 1
  med := cmed A
  med_ab a b c := by
    simp only [cayleyGraph_dist]
    exact (cmed_spec A a b c).1
  med_bc a b c := by
    simp only [cayleyGraph_dist]
    exact (cmed_spec A a b c).2.1
  med_ac a b c := by
    simp only [cayleyGraph_dist]
    exact (cmed_spec A a b c).2.2
  med_unique a b c z h1 h2 h3 := by
    simp only [cayleyGraph_dist] at h1 h2 h3
    exact median_unique A ⟨h1, h2, h3⟩ (cmed_spec A a b c)
  dim_le w t ht := by
    refine (medianGraph A hdim).dim_le w t ?_
    intro a ha
    obtain ⟨hadj, hht⟩ := ht a ha
    refine ⟨(cayleyGraph_adj_iff A).1 hadj, ?_⟩
    simpa only [cayleyGraph_dist, medianGraph] using hht

/-- **Gromov's criterion for these cube complexes, the other way round**: the square complex of
the Cayley graph is connected and simply connected. -/
theorem cayley_simplyConnected
    (hdim : ∀ t : Finset V, (∀ s ∈ t, ∀ r ∈ t, s ≠ r → A.rel s r) → t.card ≤ 3) :
    SquareComplex.SimplyConnected (cayleyMedianSimpleGraph A hdim).toSquareComplex :=
  (cayleyMedianSimpleGraph A hdim).toSquareComplex_simplyConnected

/-- The links of that square complex are flag: there are no triangles, and three neighbours
pairwise spanning squares span a three-cube. -/
theorem cayley_no_triangle
    (hdim : ∀ t : Finset V, (∀ s ∈ t, ∀ r ∈ t, s ≠ r → A.rel s r) → t.card ≤ 3)
    {a b c : CayGroup A} (hab : (cayleyGraph A).Adj a b) (hbc : (cayleyGraph A).Adj b c)
    (hca : (cayleyGraph A).Adj c a) : False :=
  (cayleyMedianSimpleGraph A hdim).no_triangle hab hbc hca

end RACG
end FiniteChains
