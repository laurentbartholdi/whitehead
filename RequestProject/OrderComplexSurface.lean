import RequestProject.BarycentricSurface

/-!
# When is the order complex of a two-dimensional cell poset a closed surface?

The nerves used by the chamber construction are comparability graphs of face posets of
two-dimensional cell structures (`RequestProject/CmpNerve.lean`), so the associated simplicial
complex is the order complex of the poset — the barycentric subdivision of the cell structure.
This file records the *combinatorial closed surface conditions* on such a poset and derives from
them the two properties which the rest of the project uses:

* `FiniteChains.ASC.SurfaceRank` — the local conditions of a two-dimensional closed cell
  structure: the rank is strictly monotone and at most two, every edge has exactly two vertices
  and lies in exactly two faces, and every vertex of a face lies in exactly two edges of that
  face;
* `FiniteChains.ASC.SurfaceRank.chain_card_le_three` — the order complex is two-dimensional;
* `FiniteChains.ASC.SurfaceRank.edgeInTwoTriangles` — **every edge of the order complex lies in
  exactly two triangles**, i.e. the subdivision is a closed pseudomanifold; this is the
  hypothesis `FiniteChains.ASC.EdgeInTwoTriangles` used by the collapse of
  `RequestProject/SurfaceBlockCollapse.lean`;
* `FiniteChains.ASC.SurfaceRank.vertexInTriangle` — every cell is a vertex of a triangle of the
  subdivision.

Edge incidences alone do not make a pseudomanifold a surface: the link of a vertex must be a
*single* cycle, not a disjoint union of cycles.  The degree conditions above already say that
every link is a disjoint union of cycles, and `FiniteChains.ASC.LinkConnected` adds the missing
condition, connectedness of the link.  A `FiniteChains.ASC.ClosedSurfacePoset` is a cell poset
satisfying both.
-/

namespace FiniteChains

namespace ASC

universe u

variable {P : Type u} [PartialOrder P]

/-- **The local conditions of a two-dimensional closed cell structure**, read on its face
poset: a rank function which is strictly monotone and at most two, exactly two vertices on
every edge, exactly two faces through every edge, and exactly two edges of a face through a
vertex of that face. -/
structure SurfaceRank (P : Type u) [PartialOrder P] where
  /-- The dimension of a cell. -/
  rk : P → ℕ
  /-- The rank increases strictly along the face order. -/
  rk_lt_of_lt : ∀ {x y : P}, x < y → rk x < rk y
  /-- The cell structure is two-dimensional. -/
  rk_le_two : ∀ x : P, rk x ≤ 2
  /-- Every edge has exactly two endpoints. -/
  two_vertices : ∀ e : P, rk e = 1 → ExactlyTwo (fun v : P => v < e)
  /-- Every edge lies in exactly two faces. -/
  two_faces : ∀ e : P, rk e = 1 → ExactlyTwo (fun f : P => e < f)
  /-- Every vertex of a face lies in exactly two edges of that face. -/
  two_edges : ∀ v f : P, rk v = 0 → rk f = 2 → v < f →
    ExactlyTwo (fun e : P => v < e ∧ e < f)
  /-- Every cell is a face of a two-dimensional cell. -/
  exists_face : ∀ x : P, ∃ f : P, rk f = 2 ∧ x ≤ f
  /-- Every two-dimensional cell has a vertex. -/
  exists_vertex : ∀ f : P, rk f = 2 → ∃ v : P, rk v = 0 ∧ v < f

namespace SurfaceRank

variable (S : SurfaceRank P)

theorem rk_eq_of_le_of_rk_le {x y : P} (S : SurfaceRank P) (h : x ≤ y) (hxy : S.rk y ≤ S.rk x) :
    x = y := by
  rcases h.lt_or_eq with hlt | rfl
  · exact absurd (S.rk_lt_of_lt hlt) (by omega)
  · rfl

/-- A cell of rank zero is minimal. -/
theorem not_lt_of_rk_zero {v x : P} (S : SurfaceRank P) (hv : S.rk v = 0) : ¬ x < v :=
  fun h => absurd (S.rk_lt_of_lt h) (by omega)

/-- A cell of rank two is maximal. -/
theorem not_lt_of_rk_two {f x : P} (S : SurfaceRank P) (hf : S.rk f = 2) : ¬ f < x :=
  fun h => absurd (S.rk_lt_of_lt h) (by have := S.rk_le_two x; omega)

end SurfaceRank

/-! ### Transfer of `ExactlyTwo` along an equivalence of predicates -/

theorem ExactlyTwo.congr {α : Sort*} {P Q : α → Prop} (h : ExactlyTwo P)
    (hPQ : ∀ x, P x ↔ Q x) : ExactlyTwo Q := by
  obtain ⟨x, y, hxy, hx, hy, huniq⟩ := h
  exact ⟨x, y, hxy, (hPQ x).1 hx, (hPQ y).1 hy, fun z hz => huniq z ((hPQ z).2 hz)⟩

/-! ### The order complex of a surface poset -/

section OrderComplex

variable [DecidableEq P]

theorem isChain_pair_iff {x y : P} :
    IsChain (· ≤ ·) (({x, y} : Finset P) : Set P) ↔ (x ≤ y ∨ y ≤ x) := by
  constructor
  · intro h
    by_cases hxy : x = y
    · exact Or.inl (le_of_eq hxy)
    · exact h (by simp) (by simp) hxy
  · intro h
    rintro a ha b hb hab
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact h
    · exact h.symm
    · exact absurd rfl hab

theorem mem_orderComplex_triple {x y z : P} (hxy : x ≤ y) :
    insert z ({x, y} : Finset P) ∈ (orderComplex P).faces ↔
      ((z ≤ x ∨ x ≤ z) ∧ (z ≤ y ∨ y ≤ z)) := by
  rw [mem_orderComplex]
  constructor
  · intro h
    rw [show ((insert z ({x, y} : Finset P) : Finset P) : Set P) = {z, x, y} by simp] at h
    have hz : z ∈ ({z, x, y} : Set P) := by simp
    have hx : x ∈ ({z, x, y} : Set P) := by simp
    have hy : y ∈ ({z, x, y} : Set P) := by simp
    exact ⟨le_or_le_of_isChain h hz hx, le_or_le_of_isChain h hz hy⟩
  · rintro ⟨hzx, hzy⟩
    rw [show ((insert z ({x, y} : Finset P) : Finset P) : Set P) = {z, x, y} by simp]
    exact isChain_triple hzx hzy (Or.inl hxy)

namespace SurfaceRank

/-- The neighbours of an edge of the order complex, described by the ranks of its two cells. -/
theorem neighbours_iff (_S : SurfaceRank P) {x y z : P} (hxy : x < y) :
    (z ∉ ({x, y} : Finset P) ∧ insert z ({x, y} : Finset P) ∈ (orderComplex P).faces) ↔
      (z ≠ x ∧ z ≠ y ∧ (z ≤ x ∨ x ≤ z) ∧ (z ≤ y ∨ y ≤ z)) := by
  rw [mem_orderComplex_triple hxy.le]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  tauto

theorem neighbours_zero_one (S : SurfaceRank P) {x y z : P} (hxy : x < y) (hx : S.rk x = 0)
    (hy : S.rk y = 1) :
    (z ∉ ({x, y} : Finset P) ∧ insert z ({x, y} : Finset P) ∈ (orderComplex P).faces) ↔
      y < z := by
  rw [neighbours_iff S hxy]
  constructor
  · rintro ⟨hzx, hzy, hcx, hcy⟩
    have hxz : x < z := by
      rcases hcx with h | h
      · exact absurd h (fun hh => hzx (S.rk_eq_of_le_of_rk_le hh (by omega)))
      · exact lt_of_le_of_ne h (Ne.symm hzx)
    rcases hcy with h | h
    · -- `z < y` would force `rk z = 0`, contradicting `x < z`
      have hzlt : z < y := lt_of_le_of_ne h hzy
      have h1 := S.rk_lt_of_lt hxz
      have h2 := S.rk_lt_of_lt hzlt
      omega
    · exact lt_of_le_of_ne h (Ne.symm hzy)
  · intro h
    have hxz : x < z := lt_trans hxy h
    exact ⟨Ne.symm hxz.ne, Ne.symm h.ne, Or.inr hxz.le, Or.inr h.le⟩

theorem neighbours_one_two (S : SurfaceRank P) {x y z : P} (hxy : x < y) (hx : S.rk x = 1)
    (hy : S.rk y = 2) :
    (z ∉ ({x, y} : Finset P) ∧ insert z ({x, y} : Finset P) ∈ (orderComplex P).faces) ↔
      z < x := by
  rw [neighbours_iff S hxy]
  constructor
  · rintro ⟨hzx, hzy, hcx, hcy⟩
    rcases hcx with h | h
    · exact lt_of_le_of_ne h hzx
    · -- `x < z` forces `rk z = 2`, and then `z` and `y` are two comparable maximal cells
      have hxz : x < z := lt_of_le_of_ne h (Ne.symm hzx)
      have hrz : S.rk z = 2 := by
        have := S.rk_lt_of_lt hxz
        have := S.rk_le_two z
        omega
      rcases hcy with h' | h'
      · exact absurd (S.rk_eq_of_le_of_rk_le h' (by omega)) hzy
      · exact absurd (S.rk_eq_of_le_of_rk_le h' (by omega)) (Ne.symm hzy)
  · intro h
    have hzy : z < y := lt_trans h hxy
    exact ⟨h.ne, hzy.ne, Or.inl h.le, Or.inl hzy.le⟩

theorem neighbours_zero_two (S : SurfaceRank P) {x y z : P} (hxy : x < y) (hx : S.rk x = 0)
    (hy : S.rk y = 2) :
    (z ∉ ({x, y} : Finset P) ∧ insert z ({x, y} : Finset P) ∈ (orderComplex P).faces) ↔
      (x < z ∧ z < y) := by
  rw [neighbours_iff S hxy]
  constructor
  · rintro ⟨hzx, hzy, hcx, hcy⟩
    have hxz : x < z := by
      rcases hcx with h | h
      · exact absurd h (fun hh => hzx (S.rk_eq_of_le_of_rk_le hh (by omega)))
      · exact lt_of_le_of_ne h (Ne.symm hzx)
    refine ⟨hxz, ?_⟩
    rcases hcy with h | h
    · exact lt_of_le_of_ne h hzy
    · exact absurd (lt_of_le_of_ne h (Ne.symm hzy)) (S.not_lt_of_rk_two hy)
  · rintro ⟨h1, h2⟩
    exact ⟨Ne.symm h1.ne, h2.ne, Or.inr h1.le, Or.inl h2.le⟩

omit [DecidableEq P] in
/-- The rank of the smaller cell of an edge of the order complex is `0` or `1`, and the possible
pairs of ranks are `(0,1)`, `(1,2)` and `(0,2)`. -/
theorem rk_cases (S : SurfaceRank P) {x y : P} (hxy : x < y) :
    (S.rk x = 0 ∧ S.rk y = 1) ∨ (S.rk x = 1 ∧ S.rk y = 2) ∨ (S.rk x = 0 ∧ S.rk y = 2) := by
  have h1 := S.rk_lt_of_lt hxy
  have h2 := S.rk_le_two y
  omega

/-- **Every edge of the order complex lies in exactly two triangles.** -/
theorem edgeInTwoTriangles (S : SurfaceRank P) : EdgeInTwoTriangles (orderComplex P) := by
  have key : ∀ x y : P, x < y →
      ExactlyTwo (fun z : P => z ∉ ({x, y} : Finset P) ∧
        insert z ({x, y} : Finset P) ∈ (orderComplex P).faces) := by
    intro x y hxy
    rcases S.rk_cases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact (S.two_faces y hy).congr (fun z => (S.neighbours_zero_one hxy hx hy).symm)
    · exact (S.two_vertices x hx).congr (fun z => (S.neighbours_one_two hxy hx hy).symm)
    · exact (S.two_edges x y hx hy hxy).congr (fun z => (S.neighbours_zero_two hxy hx hy).symm)
  intro s hs hcard
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hcard
  have hcomp : x ≤ y ∨ y ≤ x := isChain_pair_iff.1 hs
  rcases hcomp with h | h
  · exact key x y (lt_of_le_of_ne h hxy)
  · have hpair : ({x, y} : Finset P) = {y, x} := Finset.pair_comm x y
    rw [hpair]
    exact key y x (lt_of_le_of_ne h (Ne.symm hxy))

omit [DecidableEq P] in
/-- The order complex of a two-dimensional cell poset is two-dimensional. -/
theorem chain_card_le_three (S : SurfaceRank P) {s : Finset P}
    (hs : s ∈ (orderComplex P).faces) : s.card ≤ 3 := by
  classical
  have hinj : Set.InjOn S.rk (s : Set P) := by
    intro a ha b hb hab
    rcases le_or_le_of_isChain hs ha hb with h | h
    · exact S.rk_eq_of_le_of_rk_le h (le_of_eq hab.symm)
    · exact (S.rk_eq_of_le_of_rk_le h (le_of_eq hab)).symm
  have hsub : s.image S.rk ⊆ ({0, 1, 2} : Finset ℕ) := by
    intro n hn
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hn
    have := S.rk_le_two a
    interval_cases h : S.rk a <;> simp
  have hcard : (s.image S.rk).card = s.card :=
    Finset.card_image_of_injOn (by intro a ha b hb hab; exact hinj ha hb hab)
  calc s.card = (s.image S.rk).card := hcard.symm
    _ ≤ ({0, 1, 2} : Finset ℕ).card := Finset.card_le_card hsub
    _ = 3 := by decide

/-- **Every cell is a vertex of a triangle of the order complex.** -/
theorem vertexInTriangle (S : SurfaceRank P) (x : P) :
    ∃ s ∈ (orderComplex P).faces, s.card = 3 ∧ x ∈ s := by
  classical
  -- a two-cell above `x`, a vertex of it and an edge between them
  obtain ⟨f, hf, hxf⟩ := S.exists_face x
  obtain ⟨v, hv, hvf⟩ := S.exists_vertex f hf
  obtain ⟨e, -, -, ⟨hve, hef⟩, -, -⟩ := S.two_edges v f hv hf hvf
  have hchain : ({v, e, f} : Finset P) ∈ (orderComplex P).faces := by
    rw [mem_orderComplex]
    have : IsChain (· ≤ ·) ({v, e, f} : Set P) :=
      isChain_triple (Or.inl hve.le) (Or.inl (hve.trans hef).le) (Or.inl hef.le)
    simpa [Finset.coe_insert] using this
  have hcard : ({v, e, f} : Finset P).card = 3 := by
    have h1 : v ≠ e := hve.ne
    have h2 : v ≠ f := (hve.trans hef).ne
    have h3 : e ≠ f := hef.ne
    rw [Finset.card_insert_of_notMem (by simp [h1, h2]),
      Finset.card_insert_of_notMem (by simp [h3])]
    simp
  -- `x` is a face of `f`; it is `f` itself, or a vertex or an edge of `f`
  rcases eq_or_lt_of_le hxf with rfl | hlt
  · exact ⟨{v, e, x}, hchain, hcard, by simp⟩
  · have hrx : S.rk x = 0 ∨ S.rk x = 1 := by
      have := S.rk_lt_of_lt hlt
      omega
    rcases hrx with hrx | hrx
    · -- `x` is a vertex of `f`
      obtain ⟨e', -, -, ⟨hxe, he'f⟩, -, -⟩ := S.two_edges x f hrx hf hlt
      refine ⟨{x, e', f}, ?_, ?_, by simp⟩
      · rw [mem_orderComplex]
        have : IsChain (· ≤ ·) ({x, e', f} : Set P) :=
          isChain_triple (Or.inl hxe.le) (Or.inl (hxe.trans he'f).le) (Or.inl he'f.le)
        simpa [Finset.coe_insert] using this
      · have h1 : x ≠ e' := hxe.ne
        have h2 : x ≠ f := (hxe.trans he'f).ne
        have h3 : e' ≠ f := he'f.ne
        rw [Finset.card_insert_of_notMem (by simp [h1, h2]),
          Finset.card_insert_of_notMem (by simp [h3])]
        simp
    · -- `x` is an edge of `f`
      obtain ⟨w, -, -, hwx, -, -⟩ := S.two_vertices x hrx
      refine ⟨{w, x, f}, ?_, ?_, by simp⟩
      · rw [mem_orderComplex]
        have : IsChain (· ≤ ·) ({w, x, f} : Set P) :=
          isChain_triple (Or.inl hwx.le) (Or.inl (hwx.trans hlt).le) (Or.inl hlt.le)
        simpa [Finset.coe_insert] using this
      · have h1 : w ≠ x := hwx.ne
        have h2 : w ≠ f := (hwx.trans hlt).ne
        have h3 : x ≠ f := hlt.ne
        rw [Finset.card_insert_of_notMem (by simp [h1, h2]),
          Finset.card_insert_of_notMem (by simp [h3])]
        simp

end SurfaceRank

end OrderComplex

/-! ### Connected links -/

/-- The link graph of the cell `v`: the cells strictly above `v`, joined when comparable. -/
def LinkAdj (v : P) (x y : P) : Prop := v < x ∧ v < y ∧ (x ≤ y ∨ y ≤ x)

/-- **The link of every vertex is connected.**  Together with the degree conditions of
`FiniteChains.ASC.SurfaceRank` — which make every link a disjoint union of cycles — this is the
condition which distinguishes a closed surface from a pinched one. -/
def LinkConnected (S : SurfaceRank P) : Prop :=
  ∀ v : P, S.rk v = 0 → ∀ x y : P, v < x → v < y → Relation.ReflTransGen (LinkAdj v) x y

/-- **A closed surface, as a cell poset**: the local conditions of a two-dimensional closed cell
structure together with connectedness of all vertex links. -/
structure ClosedSurfacePoset (P : Type u) [PartialOrder P] where
  /-- The local incidence conditions. -/
  toSurfaceRank : SurfaceRank P
  /-- All vertex links are connected. -/
  link_connected : LinkConnected toSurfaceRank

end ASC

end FiniteChains
