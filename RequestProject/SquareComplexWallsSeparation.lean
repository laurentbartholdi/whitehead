import RequestProject.SquareComplexWallsExample
import RequestProject.SquareComplexWallsSphere

/-!
# A criterion for the separation property

`RequestProject/SquareComplexWallsSphere.lean` shows that the separation property — distinct
vertices lie on opposite sides of some wall — does not follow from connectedness and simple
connectivity alone.  This file isolates what has to be added: the standard geometric statement
*a shortest walk crosses each wall at most once*, which in the literature is proved from
nonpositive curvature by van Kampen (disk) diagrams.

* `FiniteChains.SquareComplex.crossCount` — the *number* (in `ℕ`, not modulo two) of edges of a
  walk crossing a given wall, and `FiniteChains.SquareComplex.crossCount_cast` relating it to the
  modulo-two crossing number of `RequestProject/SquareComplexWalls.lean`;
* `FiniteChains.SquareComplex.crossings_eq_side` — along any walk, the modulo-two crossing number
  of a two-sided wall is the difference of the two sides of its endpoints;
* `FiniteChains.SquareComplex.IsGeodesic` and `FiniteChains.SquareComplex.exists_geodesic` —
  shortest walks exist in a connected complex;
* `FiniteChains.SquareComplex.separation_of_geodesic_crossings` — **if every shortest walk crosses
  every wall at most once, then distinct vertices are separated by a wall**, i.e. the hypothesis
  `hsep` of `FiniteChains.SquareComplex.wallSpaceOf` holds, and
  `FiniteChains.SquareComplex.wallSpaceOf_of_geodesic_crossings` feeds it into the median dual
  complex;
* `FiniteChains.SquareComplex.exists_sepWalls_card`,
  `FiniteChains.SquareComplex.sepWalls_card_le_length` and
  `FiniteChains.SquareComplex.geodesic_crossings_of_metric` — the walls always give a lower bound
  for the distance, and the criterion is *equivalent* to the metric statement "the number of walls
  separating two vertices is their distance";
* `FiniteChains.SquareComplex.dsym_coord_eq_geodesic` — under the criterion the embedding into the
  median dual complex is isometric.

The criterion is sharp in the following sense: for the sphere of the previous file it fails in the
smallest possible way — the shortest walk `a, x, b` crosses the unique wall twice
(`FiniteChains.sphere_geodesic_crosses_twice`).
-/

namespace FiniteChains

namespace SquareComplex

universe u

variable {Vx : Type u} {S : SquareComplex Vx}

/-! ### Counting crossings in `ℕ` -/

/-- The number of edges of the walk `l` crossing the wall `χ`. -/
def crossCount (χ : Vx → Vx → ZMod 2) : List Vx → ℕ
  | a :: b :: t => (if χ a b = 1 then 1 else 0) + crossCount χ (b :: t)
  | _ => 0

@[simp] theorem crossCount_nil (χ : Vx → Vx → ZMod 2) : crossCount χ ([] : List Vx) = 0 := rfl

@[simp] theorem crossCount_singleton (χ : Vx → Vx → ZMod 2) (a : Vx) :
    crossCount χ [a] = 0 := rfl

@[simp] theorem crossCount_cons_cons (χ : Vx → Vx → ZMod 2) (a b : Vx) (t : List Vx) :
    crossCount χ (a :: b :: t) = (if χ a b = 1 then 1 else 0) + crossCount χ (b :: t) := rfl

/-- The modulo-two crossing number is the reduction of the crossing count. -/
theorem crossCount_cast (χ : Vx → Vx → ZMod 2) :
    ∀ l : List Vx, ((crossCount χ l : ℕ) : ZMod 2) = crossings χ l := by
  have hone : ∀ c : ZMod 2, (((if c = 1 then 1 else 0 : ℕ) : ℕ) : ZMod 2) = c := by decide
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
      match t with
      | [] => simp
      | b :: t' =>
          rw [crossCount_cons_cons, crossings_cons_cons, Nat.cast_add, ih, hone]

/-! ### Crossing numbers and the two sides of a wall -/

/-- Along a walk, the modulo-two crossing number of a two-sided wall is the difference between the
sides of its endpoints. -/
theorem crossings_eq_side {χ : Vx → Vx → ZMod 2} {σ : Vx → ZMod 2}
    (hside : ∀ u v : Vx, S.adj u v → σ u + σ v = χ u v) :
    ∀ (l : List Vx) (u v : Vx), S.IsWalkFrom u v l → crossings χ l = σ u + σ v := by
  have h2 : ∀ c : ZMod 2, c + c = 0 := by decide
  intro l
  induction l with
  | nil =>
      intro u v h
      exact absurd h.2.1 (by simp)
  | cons a t ih =>
      intro u v h
      obtain ⟨hw, hhead, hlast⟩ := h
      have hau : a = u := by simpa using hhead
      subst hau
      match t with
      | [] =>
          have hav : a = v := by simpa using hlast
          subst hav
          simp [h2 (σ a)]
      | b :: t' =>
          have hab : S.adj a b := (List.isChain_cons_cons.mp hw).1
          have hw' : S.IsWalk (b :: t') := (List.isChain_cons_cons.mp hw).2
          have hlast' : (b :: t').getLast? = some v := by simpa using hlast
          have htail := ih b v ⟨hw', rfl, hlast'⟩
          rw [crossings_cons_cons, htail, ← hside a b hab]
          calc σ a + σ b + (σ b + σ v) = σ a + σ v + (σ b + σ b) := by ring
            _ = σ a + σ v := by rw [h2, add_zero]

/-! ### Shortest walks -/

/-- A **geodesic**: a walk from `u` to `v` of minimal length. -/
def IsGeodesic (S : SquareComplex Vx) (u v : Vx) (l : List Vx) : Prop :=
  S.IsWalkFrom u v l ∧ ∀ m : List Vx, S.IsWalkFrom u v m → l.length ≤ m.length

/-- In a connected complex any two vertices are joined by a shortest walk. -/
theorem exists_geodesic {u v : Vx} (h : ∃ l, S.IsWalkFrom u v l) : ∃ l, S.IsGeodesic u v l := by
  classical
  set T : Set ℕ := {n | ∃ l : List Vx, S.IsWalkFrom u v l ∧ l.length = n} with hT
  have hne : T.Nonempty := by
    obtain ⟨l, hl⟩ := h
    exact ⟨l.length, l, hl, rfl⟩
  obtain ⟨l, hl, hlen⟩ : sInf T ∈ T := Nat.sInf_mem hne
  refine ⟨l, hl, ?_⟩
  intro m hm
  have hmem : m.length ∈ T := ⟨m, hm, rfl⟩
  rw [hlen]
  exact Nat.sInf_le hmem

/-- A geodesic between distinct vertices starts with an edge. -/
theorem IsGeodesic.exists_first_edge {u v : Vx} {l : List Vx} (hg : S.IsGeodesic u v l)
    (huv : u ≠ v) : ∃ (w : Vx) (t : List Vx), l = u :: w :: t ∧ S.adj u w := by
  obtain ⟨⟨hw, hhead, hlast⟩, -⟩ := hg
  match l with
  | [] => exact absurd hhead (by simp)
  | [a] =>
      exfalso
      have hau : a = u := by simpa using hhead
      have hav : a = v := by simpa using hlast
      exact huv (by rw [← hau, hav])
  | a :: b :: t =>
      have hau : a = u := by simpa using hhead
      subst hau
      exact ⟨b, t, rfl, (List.isChain_cons_cons.mp hw).1⟩

/-! ### The criterion -/

/-- **If shortest walks cross every wall at most once, distinct vertices are separated by a
wall.**  This is exactly the hypothesis `hsep` of `FiniteChains.SquareComplex.wallSpaceOf`; by
`FiniteChains.simplyConnected_not_separating` some such extra input is unavoidable, and in the
literature this one is supplied by nonpositive curvature (Gromov's link condition) through van
Kampen diagrams. -/
theorem separation_of_geodesic_crossings {ι : Type*} (W : S.WallSystem ι) {σ : ι → Vx → ZMod 2}
    (hside : ∀ (i : ι) (u v : Vx), S.adj u v → σ i u + σ i v = W.χ i u v)
    (hconn : ∀ u v : Vx, ∃ l, S.IsWalkFrom u v l)
    (hgeo : ∀ (u v : Vx) (l : List Vx), S.IsGeodesic u v l → ∀ i : ι,
      crossCount (W.χ i) l ≤ 1) :
    ∀ u v : Vx, u ≠ v → ∃ i : ι, σ i u ≠ σ i v := by
  intro u v huv
  obtain ⟨l, hg⟩ := exists_geodesic (hconn u v)
  obtain ⟨w, t, rfl, hadj⟩ := hg.exists_first_edge huv
  obtain ⟨i, hi, -⟩ := W.edge_unique u w hadj
  refine ⟨i, ?_⟩
  have hge : 1 ≤ crossCount (W.χ i) (u :: w :: t) := by
    rw [crossCount_cons_cons, if_pos hi]
    omega
  have hle : crossCount (W.χ i) (u :: w :: t) ≤ 1 := hgeo u v _ hg i
  have hcount : crossCount (W.χ i) (u :: w :: t) = 1 := le_antisymm hle hge
  have hcross : crossings (W.χ i) (u :: w :: t) = 1 := by
    rw [← crossCount_cast, hcount]
    norm_num
  have hsides : crossings (W.χ i) (u :: w :: t) = σ i u + σ i v :=
    crossings_eq_side (hside i) _ u v hg.1
  intro heq
  rw [hsides, heq] at hcross
  have h2 : σ i v + σ i v = 0 := by revert hcross; generalize σ i v = c; revert c; decide
  rw [h2] at hcross
  exact zero_ne_one hcross

/-- **Under the criterion the walls count the distance**: along a walk crossing every wall at most
once, the walls separating the endpoints are exactly the walls crossed by the walk, one for each
edge.  Applied to a geodesic (below) this says that the number of separating walls is the graph
distance, so the embedding into the median dual complex is isometric. -/
theorem exists_sepWalls_card {ι : Type*} [DecidableEq ι] (W : S.WallSystem ι)
    {σ : ι → Vx → ZMod 2}
    (hside : ∀ (i : ι) (u v : Vx), S.adj u v → σ i u + σ i v = W.χ i u v) :
    ∀ (l : List Vx) (u v : Vx), S.IsWalkFrom u v l → (∀ i : ι, crossCount (W.χ i) l ≤ 1) →
      ∃ T : Finset ι, (∀ i : ι, i ∈ T ↔ σ i u ≠ σ i v) ∧ T.card + 1 = l.length := by
  intro l
  induction l with
  | nil => intro u v h _; exact absurd h.2.1 (by simp)
  | cons p t ih =>
      intro u v h hcount
      obtain ⟨hw, hhead, hlast⟩ := h
      have hpu : p = u := by simpa using hhead
      subst hpu
      match t with
      | [] =>
          have hpv : p = v := by simpa using hlast
          subst hpv
          exact ⟨∅, by simp, by simp⟩
      | q :: t' =>
          have hpq : S.adj p q := (List.isChain_cons_cons.mp hw).1
          have hw' : S.IsWalk (q :: t') := (List.isChain_cons_cons.mp hw).2
          have hlast' : (q :: t').getLast? = some v := by simpa using hlast
          have hwalk' : S.IsWalkFrom q v (q :: t') := ⟨hw', rfl, hlast'⟩
          have hcount' : ∀ i : ι, crossCount (W.χ i) (q :: t') ≤ 1 := by
            intro i
            have := hcount i
            rw [crossCount_cons_cons] at this
            omega
          obtain ⟨T', hT'mem, hT'card⟩ := ih q v hwalk' hcount'
          obtain ⟨j, hj, hjuniq⟩ := W.edge_unique p q hpq
          -- the wall `j` of the first edge is not crossed again
          have hzero : crossCount (W.χ j) (q :: t') = 0 := by
            have h1 := hcount j
            rw [crossCount_cons_cons, if_pos hj] at h1
            omega
          have hjqv : σ j q = σ j v := by
            have hcross : crossings (W.χ j) (q :: t') = σ j q + σ j v :=
              crossings_eq_side (hside j) _ q v hwalk'
            rw [← crossCount_cast, hzero] at hcross
            have : σ j q + σ j v = 0 := by exact_mod_cast hcross.symm
            have h2 : ∀ c d : ZMod 2, c + d = 0 → c = d := by decide
            exact h2 _ _ this
          have hjpq : σ j p ≠ σ j q := by
            intro hEq
            have := hside j p q hpq
            rw [hEq, hj] at this
            have h2 : ∀ c : ZMod 2, c + c ≠ 1 := by decide
            exact h2 _ this
          have hjnot : j ∉ T' := by
            intro hmem
            exact ((hT'mem j).1 hmem) hjqv
          refine ⟨insert j T', ?_, ?_⟩
          · intro i
            by_cases hij : i = j
            · subst hij
              simp only [Finset.mem_insert, true_or, true_iff]
              rw [hjqv] at hjpq
              exact hjpq
            · have hiedge : W.χ i p q = 0 := by
                by_contra hne
                have h2 : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
                exact hij (hjuniq i (h2 _ hne))
              have hipq : σ i p = σ i q := by
                have := hside i p q hpq
                rw [hiedge] at this
                have h2 : ∀ c d : ZMod 2, c + d = 0 → c = d := by decide
                exact h2 _ _ this
              rw [Finset.mem_insert, hipq]
              simp only [hij, false_or]
              exact hT'mem i
          · rw [Finset.card_insert_of_notMem hjnot]
            simp only [List.length_cons] at hT'card ⊢
            omega

/-- **The number of walls separating two vertices is their distance**, whenever shortest walks
cross every wall at most once. -/
theorem sepWalls_card_of_geodesic {ι : Type*} [DecidableEq ι] (W : S.WallSystem ι)
    {σ : ι → Vx → ZMod 2}
    (hside : ∀ (i : ι) (u v : Vx), S.adj u v → σ i u + σ i v = W.χ i u v)
    (hgeo : ∀ (u v : Vx) (l : List Vx), S.IsGeodesic u v l → ∀ i : ι,
      crossCount (W.χ i) l ≤ 1)
    {u v : Vx} {l : List Vx} (hg : S.IsGeodesic u v l) :
    ∃ T : Finset ι, (∀ i : ι, i ∈ T ↔ σ i u ≠ σ i v) ∧ T.card + 1 = l.length :=
  exists_sepWalls_card W hside l u v hg.1 (hgeo u v l hg)

/-- **Walls bound the distance, and equality is exactly the criterion.**  For any walk, the number
of walls separating its endpoints is at most the number of its edges; and if the two are equal then
the walk crosses every wall at most once.  Combined with
`FiniteChains.SquareComplex.exists_sepWalls_card` this makes the criterion equivalent to the
metric statement "the graph distance is the number of separating walls". -/
theorem sepWalls_card_le_length {ι : Type*} [DecidableEq ι] (W : S.WallSystem ι)
    {σ : ι → Vx → ZMod 2}
    (hside : ∀ (i : ι) (u v : Vx), S.adj u v → σ i u + σ i v = W.χ i u v) :
    ∀ (l : List Vx) (u v : Vx), S.IsWalkFrom u v l → ∀ T : Finset ι,
      (∀ i : ι, i ∈ T ↔ σ i u ≠ σ i v) →
        T.card + 1 ≤ l.length ∧
          (T.card + 1 = l.length → ∀ i : ι, crossCount (W.χ i) l ≤ 1) := by
  have hsum : ∀ c d : ZMod 2, c + d = 0 → c = d := by decide
  have hne1 : ∀ c : ZMod 2, c + c ≠ 1 := by decide
  have hnz : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  have hthree : ∀ c d e : ZMod 2, c ≠ d → c ≠ e → d = e := by decide
  have hthree' : ∀ c d e : ZMod 2, c ≠ d → c = e → d ≠ e := by decide
  intro l
  induction l with
  | nil => intro u v h; exact absurd h.2.1 (by simp)
  | cons p t ih =>
      intro u v h T hT
      obtain ⟨hw, hhead, hlast⟩ := h
      have hpu : p = u := by simpa using hhead
      subst hpu
      match t with
      | [] =>
          have hpv : p = v := by simpa using hlast
          subst hpv
          have hTempty : T = ∅ := by
            refine Finset.eq_empty_of_forall_notMem ?_
            intro i hi
            exact ((hT i).1 hi) rfl
          subst hTempty
          refine ⟨by simp, ?_⟩
          intro _ i
          simp [crossCount]
      | q :: t' =>
          have hpq : S.adj p q := (List.isChain_cons_cons.mp hw).1
          have hw' : S.IsWalk (q :: t') := (List.isChain_cons_cons.mp hw).2
          have hlast' : (q :: t').getLast? = some v := by simpa using hlast
          have hwalk' : S.IsWalkFrom q v (q :: t') := ⟨hw', rfl, hlast'⟩
          obtain ⟨j, hj, hjuniq⟩ := W.edge_unique p q hpq
          have hjpq : σ j p ≠ σ j q := by
            intro hEq
            have := hside j p q hpq
            rw [hEq, hj] at this
            exact hne1 _ this
          have hother : ∀ i : ι, i ≠ j → σ i p = σ i q := by
            intro i hij
            have hiedge : W.χ i p q = 0 := by
              by_contra hne
              exact hij (hjuniq i (hnz _ hne))
            have := hside i p q hpq
            rw [hiedge] at this
            exact hsum _ _ this
          -- the separating set of the tail
          set T' : Finset ι := if j ∈ T then T.erase j else insert j T with hT'def
          have hT'mem : ∀ i : ι, i ∈ T' ↔ σ i q ≠ σ i v := by
            intro i
            by_cases hij : i = j
            · subst hij
              by_cases hjT : i ∈ T
              · have hpv : σ i p ≠ σ i v := (hT i).1 hjT
                have : σ i q = σ i v := hthree _ _ _ hjpq hpv
                simp [hT'def, hjT, this]
              · have hpv : σ i p = σ i v := by
                  by_contra hne
                  exact hjT ((hT i).2 hne)
                have : σ i q ≠ σ i v := (hthree' _ _ _ hjpq hpv)
                simp [hT'def, hjT, this]
            · have hpq' := hother i hij
              by_cases hjT : j ∈ T
              · rw [hT'def]
                simp only [if_pos hjT, Finset.mem_erase]
                rw [hT i, hpq']
                exact and_iff_right hij
              · rw [hT'def]
                simp only [if_neg hjT, Finset.mem_insert, hij, false_or]
                rw [hT i, hpq']
          obtain ⟨hle', heq'⟩ := ih q v hwalk' T' hT'mem
          have hcard : (j ∈ T → T.card = T'.card + 1) ∧ (j ∉ T → T'.card = T.card + 1) := by
            constructor
            · intro hjT
              rw [hT'def, if_pos hjT, Finset.card_erase_of_mem hjT]
              have : 1 ≤ T.card := Finset.card_pos.2 ⟨j, hjT⟩
              omega
            · intro hjT
              rw [hT'def, if_neg hjT, Finset.card_insert_of_notMem hjT]
          refine ⟨?_, ?_⟩
          · by_cases hjT : j ∈ T
            · have := hcard.1 hjT
              simp only [List.length_cons] at hle' ⊢
              omega
            · have := hcard.2 hjT
              simp only [List.length_cons] at hle' ⊢
              omega
          · intro heq i
            have hjT : j ∈ T := by
              by_contra hjT
              have := hcard.2 hjT
              simp only [List.length_cons] at hle' heq
              omega
            have hcardT := hcard.1 hjT
            have heqtail : T'.card + 1 = (q :: t').length := by
              simp only [List.length_cons] at heq ⊢
              omega
            have htail := heq' heqtail
            have hjnot : j ∉ T' := by
              rw [hT'def, if_pos hjT]
              exact Finset.notMem_erase j T
            have hjqv : σ j q = σ j v := by
              by_contra hne
              exact hjnot ((hT'mem j).2 hne)
            have hzero : crossCount (W.χ j) (q :: t') = 0 := by
              have hcross : crossings (W.χ j) (q :: t') = σ j q + σ j v :=
                crossings_eq_side (hside j) _ q v hwalk'
              rw [hjqv] at hcross
              have h2 : ∀ c : ZMod 2, c + c = 0 := by decide
              rw [h2, ← crossCount_cast] at hcross
              have hle1 := htail j
              have : crossCount (W.χ j) (q :: t') = 0 ∨ crossCount (W.χ j) (q :: t') = 1 := by
                omega
              rcases this with h0 | h1
              · exact h0
              · rw [h1] at hcross
                exact absurd hcross (by decide)
            by_cases hij : i = j
            · subst hij
              rw [crossCount_cons_cons, if_pos hj, hzero]
            · have hiedge : W.χ i p q ≠ 1 := by
                intro hc
                exact hij (hjuniq i hc)
              rw [crossCount_cons_cons, if_neg hiedge]
              simpa using htail i

/-- **The metric form of the criterion.**  If the number of walls separating two vertices is always
the number of edges of a shortest walk between them, then shortest walks cross every wall at most
once — hence, by `FiniteChains.SquareComplex.separation_of_geodesic_crossings`, distinct vertices
are separated.  With `FiniteChains.SquareComplex.exists_sepWalls_card` the two forms are
equivalent. -/
theorem geodesic_crossings_of_metric {ι : Type*} [DecidableEq ι] (W : S.WallSystem ι)
    {σ : ι → Vx → ZMod 2}
    (hside : ∀ (i : ι) (u v : Vx), S.adj u v → σ i u + σ i v = W.χ i u v)
    (hsepfin : ∀ u v : Vx, ∃ T : Finset ι, ∀ i : ι, i ∈ T ↔ σ i u ≠ σ i v)
    (hmetric : ∀ (u v : Vx) (l : List Vx), S.IsGeodesic u v l → ∀ T : Finset ι,
      (∀ i : ι, i ∈ T ↔ σ i u ≠ σ i v) → T.card + 1 = l.length) :
    ∀ (u v : Vx) (l : List Vx), S.IsGeodesic u v l → ∀ i : ι, crossCount (W.χ i) l ≤ 1 := by
  intro u v l hg i
  obtain ⟨T, hT⟩ := hsepfin u v
  exact (sepWalls_card_le_length W hside l u v hg.1 T hT).2 (hmetric u v l hg T hT) i

/-- The criterion feeds the vertices of the complex into a wall space, and hence — by
`FiniteChains.SquareComplex.wallSpaceOf_coord_injective` — injectively into the median dual cube
complex. -/
def wallSpaceOf_of_geodesic_crossings {ι : Type*} (W : S.WallSystem ι) {σ : ι → Vx → ZMod 2}
    {x₀ : Vx} (hfin : ∀ v : Vx, {i : ι | σ i v ≠ σ i x₀}.Finite)
    (hside : ∀ (i : ι) (u v : Vx), S.adj u v → σ i u + σ i v = W.χ i u v)
    (hconn : ∀ u v : Vx, ∃ l, S.IsWalkFrom u v l)
    (hgeo : ∀ (u v : Vx) (l : List Vx), S.IsGeodesic u v l → ∀ i : ι,
      crossCount (W.χ i) l ≤ 1) :
    WallSpace Vx ι :=
  wallSpaceOf hfin (separation_of_geodesic_crossings W hside hconn hgeo)

open RollerBridge in
/-- **The embedding into the median dual complex is isometric**: under the criterion the number of
coordinates in which two vertices differ is the number of edges of a shortest walk joining them.
Together with `FiniteChains.SquareComplex.wallSpaceOf_dsym_adj` and the results on the dual of a
wall space, this identifies the one-skeleton of the complex with a subgraph of a median graph, on
the nose. -/
theorem dsym_coord_eq_geodesic {ι : Type*} [DecidableEq ι] (W : S.WallSystem ι)
    {σ : ι → Vx → ZMod 2} {x₀ : Vx} (hfin : ∀ v : Vx, {i : ι | σ i v ≠ σ i x₀}.Finite)
    (hside : ∀ (i : ι) (u v : Vx), S.adj u v → σ i u + σ i v = W.χ i u v)
    (hconn : ∀ u v : Vx, ∃ l, S.IsWalkFrom u v l)
    (hgeo : ∀ (u v : Vx) (l : List Vx), S.IsGeodesic u v l → ∀ i : ι,
      crossCount (W.χ i) l ≤ 1)
    (y₀ : Vx) {u v : Vx} {l : List Vx} (hg : S.IsGeodesic u v l) :
    dsym ((wallSpaceOf_of_geodesic_crossings W hfin hside hconn hgeo).coord y₀ u)
        ((wallSpaceOf_of_geodesic_crossings W hfin hside hconn hgeo).coord y₀ v) + 1 =
      l.length := by
  classical
  set WS := wallSpaceOf_of_geodesic_crossings W hfin hside hconn hgeo
  obtain ⟨T, hTmem, hTcard⟩ := sepWalls_card_of_geodesic W hside hgeo hg
  have hsets : (WS.fin u v).toFinset = T := by
    ext i
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, hTmem i]
    constructor
    · intro h; exact ne_of_decide_ne h
    · intro h; exact decide_ne_of_ne h
  rw [WallSpace.dsym_coord, hsets, hTcard]

end SquareComplex

/-! ### Sharpness: on the sphere a geodesic crosses the wall twice -/

/-- Any walk from `a` to `b` in the sphere has at least three vertices: the two are not adjacent. -/
theorem sphere_walk_a_b_length {m : List SphereV} (hm : sphereCx.IsWalkFrom .a .b m) :
    3 ≤ m.length := by
  obtain ⟨hw, hhead, hlast⟩ := hm
  match m with
  | [] => exact absurd hhead (by simp)
  | [p] =>
      exfalso
      have h1 : p = SphereV.a := by simpa using hhead
      have h2 : p = SphereV.b := by simpa using hlast
      rw [h1] at h2
      exact absurd h2 (by decide)
  | [p, q] =>
      exfalso
      have h1 : p = SphereV.a := by simpa using hhead
      have h2 : q = SphereV.b := by simpa using hlast
      have hadj : sphereCx.adj p q := (List.isChain_cons_cons.mp hw).1
      rw [h1, h2] at hadj
      exact absurd hadj (by decide)
  | p :: q :: r :: t => simp only [List.length_cons]; omega

/-- The walk `a, x, b` is a shortest walk from `a` to `b`. -/
theorem sphere_geodesic_axb : sphereCx.IsGeodesic .a .b [.a, .x, .b] := by
  refine ⟨⟨sphere_isWalk (by decide), rfl, rfl⟩, ?_⟩
  intro m hm
  simpa using sphere_walk_a_b_length hm

/-- **The criterion fails on the sphere in the smallest possible way**: the shortest walk
`a, x, b` crosses the unique wall twice.  This is the exact point at which nonpositive curvature
is needed. -/
theorem sphere_geodesic_crosses_twice :
    SquareComplex.crossCount (sphereWallSystem.χ ()) [.a, .x, .b] = 2 := by
  decide

/-! ### Non-vacuity: the criterion holds for the four-cycle

For the four-cycle with its square glued in the criterion can be checked by hand, and it yields the
separation property — hence the median embedding — unconditionally. -/

instance : DecidableRel cycleFour.adj := fun u v => inferInstanceAs (Decidable (cycleFourAdj u v))

instance (l : List (ZMod 4)) : Decidable (cycleFour.IsWalk l) :=
  inferInstanceAs (Decidable (List.IsChain cycleFourAdj l))

instance (u v : ZMod 4) (l : List (ZMod 4)) : Decidable (cycleFour.IsWalkFrom u v l) :=
  inferInstanceAs (Decidable (cycleFour.IsWalk l ∧ l.head? = some u ∧ l.getLast? = some v))

/-- An explicit walk of at most three vertices between any two vertices of the four-cycle. -/
def cycleFourPath (u v : ZMod 4) : List (ZMod 4) :=
  if u = v then [u] else if cycleFourAdj u v then [u, v] else [u, u + 1, v]

theorem cycleFour_short_walk : ∀ u v : ZMod 4,
    cycleFour.IsWalkFrom u v (cycleFourPath u v) ∧ (cycleFourPath u v).length ≤ 3 := by decide

/-- Every shortest walk of the four-cycle has at most three vertices. -/
theorem cycleFour_geodesic_length {u v : ZMod 4} {l : List (ZMod 4)}
    (hg : cycleFour.IsGeodesic u v l) : l.length ≤ 3 :=
  le_trans (hg.2 _ (cycleFour_short_walk u v).1) (cycleFour_short_walk u v).2

theorem cycleFour_three_crossing : ∀ (p q r : ZMod 4) (i : Bool), cycleFourAdj p q →
    cycleFourAdj q r → p ≠ r → ¬ cycleFourAdj p r →
    SquareComplex.crossCount (cycleFourWalls i) [p, q, r] ≤ 1 := by decide

/-- **The criterion holds for the four-cycle**: a shortest walk crosses each of its two walls at
most once. -/
theorem cycleFour_geodesic_crossings : ∀ (u v : ZMod 4) (l : List (ZMod 4)),
    cycleFour.IsGeodesic u v l → ∀ i : Bool,
      SquareComplex.crossCount (cycleFourWalls i) l ≤ 1 := by
  intro u v l hg i
  have hlen := cycleFour_geodesic_length hg
  obtain ⟨⟨hw, hhead, hlast⟩, hmin⟩ := hg
  match l with
  | [] => simp [SquareComplex.crossCount]
  | [p] => simp [SquareComplex.crossCount]
  | [p, q] =>
      rw [SquareComplex.crossCount_cons_cons, SquareComplex.crossCount_singleton]
      split <;> omega
  | [p, q, r] =>
      have hpu : p = u := by simpa using hhead
      have hrv : r = v := by simpa using hlast
      subst hpu; subst hrv
      have hpq : cycleFourAdj p q := (List.isChain_cons_cons.mp hw).1
      have hqr : cycleFourAdj q r :=
        (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hw).2).1
      have hne : p ≠ r := by
        intro h
        subst h
        have : (3 : ℕ) ≤ ([p] : List (ZMod 4)).length :=
          hmin [p] ⟨List.isChain_singleton .., rfl, rfl⟩
        simp at this
      have hnadj : ¬ cycleFourAdj p r := by
        intro h
        have : (3 : ℕ) ≤ ([p, r] : List (ZMod 4)).length :=
          hmin [p, r] ⟨List.isChain_cons_cons.mpr ⟨h, List.isChain_singleton ..⟩, rfl, rfl⟩
        simp at this
      exact cycleFour_three_crossing p q r i hpq hqr hne hnadj
  | p :: q :: r :: s :: t =>
      exfalso
      simp only [List.length_cons] at hlen
      omega

/-- **The four-cycle satisfies the separation property**, by the criterion: its halfspace
coordinates distinguish distinct vertices, so its vertices embed into the median dual cube
complex with no extra hypothesis. -/
theorem cycleFour_separation :
    ∃ σ : Bool → ZMod 4 → ZMod 2,
      (∀ i, σ i 0 = 0) ∧
      (∀ (i : Bool) (u v : ZMod 4), cycleFour.adj u v → σ i u + σ i v = cycleFourWalls i u v) ∧
      (∀ u v : ZMod 4, u ≠ v → ∃ i : Bool, σ i u ≠ σ i v) := by
  obtain ⟨σ, hbase, hside, -, -⟩ := cycleFour_rollerCoordinates
  refine ⟨σ, hbase, hside, ?_⟩
  refine SquareComplex.separation_of_geodesic_crossings cycleFourWallSystem hside ?_
    cycleFour_geodesic_crossings
  intro u v
  exact ⟨cycleFourPath u v, (cycleFour_short_walk u v).1⟩

end FiniteChains
