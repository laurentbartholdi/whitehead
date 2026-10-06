import Mathlib

/-!
# Walls (hyperplanes) of a simply connected square complex

The remaining geometric input of the paper, in the branch developed in
`RequestProject/CubeCartanHadamard.lean`, `RequestProject/CubeRollerModel.lean` and
`RequestProject/CubeMedianGraph.lean`, is the criterion

> a simply connected cube complex with flag links has median one–skeleton

(Gromov's link condition together with Chepoi's theorem).  Its first half — the half that is
responsible for *hyperplanes*, i.e. for the halfspace (Roller) coordinates used in
`FiniteChains.RollerModel` — is purely combinatorial and is proved here from scratch, with no
finiteness, local finiteness or dimension assumption:

*in a simply connected square complex every square-closed family of edges (in particular every
hyperplane) is two-sided: it is the set of edges joining the two sides of a partition of the
vertex set.*

Everything is elementary and self-contained:

* `FiniteChains.SquareComplex` — a graph together with a set of squares (two-cells), closed under
  rotating and reversing the cyclic order of the four vertices;
* walks are lists of vertices (`List.IsChain S.adj`), and `FiniteChains.SquareComplex.Move` is the
  elementary combinatorial homotopy: cancelling a backtrack `x, y, x ↝ x`, and pushing a path
  across a square `a, b, c ↝ a, d, c`;
* `FiniteChains.SquareComplex.SimplyConnected` says that every closed walk is homotopic to the
  constant walk.

The main results are

* `FiniteChains.SquareComplex.crossings_homotopic` — the number of edges of a walk lying in a
  square-closed family is a homotopy invariant modulo two;
* `FiniteChains.SquareComplex.crossings_eq_zero_of_closed` — hence it vanishes on closed walks of a
  simply connected complex;
* `FiniteChains.SquareComplex.exists_side` — hence, over a connected complex, every square-closed
  family `χ` of edges is the set of edges separating the two sides of a two-colouring `σ` of the
  vertices: `σ u + σ v = χ u v` for every edge `u v`;
* `FiniteChains.SquareComplex.exists_bipartition` — with the family of *all* edges: the
  one-skeleton of a connected simply connected square complex is bipartite (as the one-skeleton of a
  median graph must be);
* `FiniteChains.SquareComplex.closed_walk_length_odd` — equivalently, all closed walks have even
  length;
* `FiniteChains.SquareComplex.exists_side_edge` — an edge lying in no square separates the complex;
* `FiniteChains.SquareComplex.triangle_side_in_square` — hence every triangle has a side lying in a
  square; with the flag/dimension conditions of the cube complexes considered in the paper this is
  the absence of triangles.

Non-vacuity is checked on two explicit complexes: the complex with two vertices and one edge
(`FiniteChains.edgeComplex`) and the four-cycle with its square glued in
(`FiniteChains.cycleFour`, `FiniteChains.cycleFour_simplyConnected`), the latter containing a
genuine two-cell.  That the square is really needed is also checked: the four-cycle *without* the
square is not simply connected (`FiniteChains.cycleFourNoSquare_not_simplyConnected`).
-/

namespace FiniteChains

universe u

/-- A **square complex**, recorded combinatorially: a simple graph (`adj`) together with a
predicate `sq a b c d` saying that `a, b, c, d` are, in this cyclic order, the vertices of a
two-cell.  The last two axioms say that the set of squares does not depend on where the cyclic
order is started nor on its orientation. -/
structure SquareComplex (Vx : Type u) where
  /-- Adjacency of the one-skeleton. -/
  adj : Vx → Vx → Prop
  /-- Adjacency is symmetric. -/
  adj_symm : ∀ {a b : Vx}, adj a b → adj b a
  /-- There are no loops. -/
  adj_irrefl : ∀ a : Vx, ¬ adj a a
  /-- `sq a b c d` : the four vertices span a two-cell, in this cyclic order. -/
  sq : Vx → Vx → Vx → Vx → Prop
  /-- The four sides of a square are edges. -/
  sq_adj : ∀ {a b c d : Vx}, sq a b c d → adj a b ∧ adj b c ∧ adj c d ∧ adj d a
  /-- Squares may be read starting at any of their vertices. -/
  sq_rotate : ∀ {a b c d : Vx}, sq a b c d → sq b c d a
  /-- Squares may be read in either orientation. -/
  sq_reverse : ∀ {a b c d : Vx}, sq a b c d → sq d c b a

namespace SquareComplex

variable {Vx : Type u} {S : SquareComplex Vx}

/-- A walk is a list of vertices in which consecutive vertices are adjacent. -/
def IsWalk (S : SquareComplex Vx) (l : List Vx) : Prop := List.IsChain S.adj l

/-- A walk from `x` to `y`. -/
def IsWalkFrom (S : SquareComplex Vx) (x y : Vx) (l : List Vx) : Prop :=
  S.IsWalk l ∧ l.head? = some x ∧ l.getLast? = some y

/-- A closed walk based at `x`. -/
def IsClosedWalk (S : SquareComplex Vx) (x : Vx) (l : List Vx) : Prop := S.IsWalkFrom x x l

/-- The elementary homotopies of walks: cancelling a backtrack, pushing across a square, and
performing either of these after a common initial vertex. -/
inductive Move (S : SquareComplex Vx) : List Vx → List Vx → Prop
  /-- Cancel the backtrack `x, y, x`. -/
  | backtrack (x y : Vx) (q : List Vx) : Move S (x :: y :: x :: q) (x :: q)
  /-- Push the path `a, b, c` across the square `a, b, c, d` to the path `a, d, c`. -/
  | square {a b c d : Vx} (h : S.sq a b c d) (q : List Vx) :
      Move S (a :: b :: c :: q) (a :: d :: c :: q)
  /-- Perform a move after a common initial vertex. -/
  | cons (x : Vx) {l l' : List Vx} : Move S l l' → Move S (x :: l) (x :: l')

/-- Combinatorial homotopy of walks: the equivalence relation generated by the elementary
moves. -/
def Homotopic (S : SquareComplex Vx) (l l' : List Vx) : Prop :=
  Relation.ReflTransGen (fun p q => S.Move p q ∨ S.Move q p) l l'

theorem Homotopic.refl (l : List Vx) : S.Homotopic l l := Relation.ReflTransGen.refl

theorem Homotopic.trans {l l' l'' : List Vx} (h : S.Homotopic l l') (h' : S.Homotopic l' l'') :
    S.Homotopic l l'' := Relation.ReflTransGen.trans h h'

theorem Homotopic.of_move {l l' : List Vx} (h : S.Move l l') : S.Homotopic l l' :=
  Relation.ReflTransGen.single (Or.inl h)

theorem Homotopic.head_move {l l' l'' : List Vx} (h : S.Move l l') (h' : S.Homotopic l' l'') :
    S.Homotopic l l'' := Relation.ReflTransGen.head (Or.inl h) h'

/-! ### Moves preserve walks and their endpoints -/

theorem Move.head?_eq {l l' : List Vx} (h : S.Move l l') : l.head? = l'.head? := by
  induction h with
  | backtrack x y q => rfl
  | square h q => rfl
  | cons x _ _ => rfl

theorem Move.ne_nil {l l' : List Vx} (h : S.Move l l') : l ≠ [] ∧ l' ≠ [] := by
  induction h with
  | backtrack x y q => exact ⟨by simp, by simp⟩
  | square h q => exact ⟨by simp, by simp⟩
  | cons x _ ih => exact ⟨by simp, by simp⟩

theorem Move.getLast?_eq {l l' : List Vx} (h : S.Move l l') : l.getLast? = l'.getLast? := by
  induction h with
  | backtrack x y q => simp
  | square h q => simp
  | cons x hm ih =>
      rcases hm.ne_nil with ⟨h1, h2⟩
      rcases List.exists_cons_of_ne_nil h1 with ⟨a, t, rfl⟩
      rcases List.exists_cons_of_ne_nil h2 with ⟨b, t', rfl⟩
      simpa using ih

theorem Move.isWalk {l l' : List Vx} (h : S.Move l l') (hl : S.IsWalk l) : S.IsWalk l' := by
  induction h with
  | backtrack x y q =>
      rw [IsWalk, List.isChain_cons_cons] at hl
      exact hl.2.tail
  | square h q =>
      obtain ⟨hab, hbc, hcd, hda⟩ := S.sq_adj h
      rw [IsWalk, List.isChain_cons_cons] at hl ⊢
      refine ⟨S.adj_symm hda, ?_⟩
      rw [List.isChain_cons_cons] at hl ⊢
      exact ⟨S.adj_symm hcd, hl.2.2⟩
  | cons x hm ih =>
      rcases hm.ne_nil with ⟨h1, h2⟩
      rcases List.exists_cons_of_ne_nil h1 with ⟨a, t, rfl⟩
      rcases List.exists_cons_of_ne_nil h2 with ⟨b, t', rfl⟩
      rw [IsWalk, List.isChain_cons_cons] at hl ⊢
      have hhead := hm.head?_eq
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      exact ⟨hl.1, ih hl.2⟩

/-- Elementary moves take closed walks to closed walks with the same base point. -/
theorem IsClosedWalk.of_move {x : Vx} {l l' : List Vx} (hm : S.Move l l')
    (h : S.IsClosedWalk x l) : S.IsClosedWalk x l' :=
  ⟨hm.isWalk h.1, by rw [← hm.head?_eq]; exact h.2.1, by rw [← hm.getLast?_eq]; exact h.2.2⟩

theorem Homotopic.head?_eq {l l' : List Vx} (h : S.Homotopic l l') : l.head? = l'.head? := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rcases hstep with hm | hm
                       · exact ih.trans hm.head?_eq
                       · exact ih.trans hm.head?_eq.symm

theorem Homotopic.getLast?_eq {l l' : List Vx} (h : S.Homotopic l l') :
    l.getLast? = l'.getLast? := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => rcases hstep with hm | hm
                       · exact ih.trans hm.getLast?_eq
                       · exact ih.trans hm.getLast?_eq.symm

/-! ### Crossing numbers -/

/-- The number, modulo two, of edges of the walk `l` carrying the label `χ`. -/
def crossings (χ : Vx → Vx → ZMod 2) : List Vx → ZMod 2
  | a :: b :: t => χ a b + crossings χ (b :: t)
  | _ => 0

@[simp] theorem crossings_nil (χ : Vx → Vx → ZMod 2) : crossings χ [] = 0 := rfl

@[simp] theorem crossings_singleton (χ : Vx → Vx → ZMod 2) (a : Vx) : crossings χ [a] = 0 := rfl

@[simp] theorem crossings_cons_cons (χ : Vx → Vx → ZMod 2) (a b : Vx) (t : List Vx) :
    crossings χ (a :: b :: t) = χ a b + crossings χ (b :: t) := rfl

/-- A **wall label**: a symmetric labelling of the edges by `ZMod 2` taking the same value on
opposite sides of every square.  The characteristic function of a hyperplane — a family of edges
closed under the relation "opposite sides of a square" — is such a labelling. -/
structure IsWallLabel (S : SquareComplex Vx) (χ : Vx → Vx → ZMod 2) : Prop where
  /-- The labelling does not depend on the direction of the edge. -/
  symm : ∀ a b : Vx, χ a b = χ b a
  /-- Opposite sides of a square carry the same label. -/
  square : ∀ {a b c d : Vx}, S.sq a b c d → χ a b = χ c d

theorem crossings_glue (χ : Vx → Vx → ZMod 2) {v : Vx} :
    ∀ {l m : List Vx}, l.getLast? = some v → m.head? = some v →
      crossings χ (l ++ m.tail) = crossings χ l + crossings χ m := by
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
          simp only [List.cons_append, crossings_cons_cons]
          rw [show (b :: l') ++ m.tail = b :: (l' ++ m.tail) from rfl] at this
          rw [this]
          ring

theorem crossings_reverse {χ : Vx → Vx → ZMod 2} (hsymm : ∀ a b : Vx, χ a b = χ b a) :
    ∀ l : List Vx, crossings χ l.reverse = crossings χ l := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
      match t with
      | [] => simp
      | b :: t' =>
          have hlast : (b :: t').reverse.getLast? = some b := by
            simp
          have hhead : ([b, a] : List Vx).head? = some b := rfl
          have hglue := crossings_glue χ hlast hhead
          have heq : (b :: t').reverse ++ ([b, a] : List Vx).tail = (a :: b :: t').reverse := by
            simp
          rw [heq, ih] at hglue
          rw [hglue]
          simp only [crossings_cons_cons, crossings_singleton, add_zero]
          rw [hsymm b a]
          ring

theorem crossings_move {χ : Vx → Vx → ZMod 2} (hχ : S.IsWallLabel χ) {l l' : List Vx}
    (h : S.Move l l') : crossings χ l = crossings χ l' := by
  have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
  induction h with
  | backtrack x y q =>
      simp only [crossings_cons_cons]
      rw [hχ.symm y x, ← add_assoc, h2, zero_add]
  | @square a b c d hsq q =>
      have h1 : χ a b = χ c d := hχ.square hsq
      have h2' : χ b c = χ d a := hχ.square (S.sq_rotate hsq)
      simp only [crossings_cons_cons]
      rw [h1, h2', hχ.symm c d, hχ.symm d a]
      ring
  | cons x hm ih =>
      rcases hm.ne_nil with ⟨hne, hne'⟩
      rcases List.exists_cons_of_ne_nil hne with ⟨a, t, rfl⟩
      rcases List.exists_cons_of_ne_nil hne' with ⟨b, t', rfl⟩
      have hhead := hm.head?_eq
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      simp only [crossings_cons_cons, ih]

theorem crossings_homotopic {χ : Vx → Vx → ZMod 2} (hχ : S.IsWallLabel χ) {l l' : List Vx}
    (h : S.Homotopic l l') : crossings χ l = crossings χ l' := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      rcases hstep with hm | hm
      · exact ih.trans (crossings_move hχ hm)
      · exact ih.trans (crossings_move hχ hm).symm

/-! ### Simple connectivity -/

/-- A square complex is **simply connected** when every closed walk can be contracted to its base
point by elementary moves. -/
def SimplyConnected (S : SquareComplex Vx) : Prop :=
  ∀ (x : Vx) (l : List Vx), S.IsClosedWalk x l → S.Homotopic l [x]

/-- **Every wall label has even total crossing number on a closed walk of a simply connected square
complex.** -/
theorem crossings_eq_zero_of_closed (hSC : S.SimplyConnected) {χ : Vx → Vx → ZMod 2}
    (hχ : S.IsWallLabel χ) {x : Vx} {l : List Vx} (hl : S.IsClosedWalk x l) :
    crossings χ l = 0 := by
  have := crossings_homotopic hχ (hSC x l hl)
  simpa using this

/-! ### Two walks with the same endpoints have the same crossing numbers -/

theorem isWalk_reverse {l : List Vx} (h : S.IsWalk l) : S.IsWalk l.reverse := by
  rw [IsWalk, List.isChain_reverse]
  exact h.imp (by intro a b hab; exact S.adj_symm hab)

theorem isWalk_junction {y z : Vx} {r : List Vx} (h : S.IsWalk (y :: r))
    (hz : r.head? = some z) : S.adj y z := by
  cases r with
  | nil => simp at hz
  | cons c r' =>
      simp only [List.head?_cons, Option.some.injEq] at hz
      subst hz
      exact (List.isChain_cons_cons.mp h).1

theorem crossings_eq_of_walkFrom (hSC : S.SimplyConnected) {χ : Vx → Vx → ZMod 2}
    (hχ : S.IsWallLabel χ) {x y : Vx} {p q : List Vx} (hp : S.IsWalkFrom x y p)
    (hq : S.IsWalkFrom x y q) : crossings χ p = crossings χ q := by
  obtain ⟨hpw, hph, hpl⟩ := hp
  obtain ⟨hqw, hqh, hql⟩ := hq
  have hqr : S.IsWalk q.reverse := isWalk_reverse hqw
  have hqrh : q.reverse.head? = some y := by simpa using hql
  have hqrl : q.reverse.getLast? = some x := by simpa using hqh
  obtain ⟨b, r, hbr⟩ : ∃ b r, q.reverse = b :: r := by
    cases hq' : q.reverse with
    | nil => rw [hq'] at hqrh; simp at hqrh
    | cons b r => exact ⟨b, r, rfl⟩
  have hby : b = y := by rw [hbr] at hqrh; simpa using hqrh
  subst hby
  have hpne : p ≠ [] := by
    intro h; rw [h] at hph; simp at hph
  -- the concatenation `p ++ q.reverse.tail` is a closed walk at `x`
  have hwalk : S.IsWalk (p ++ q.reverse.tail) := by
    rw [IsWalk, List.isChain_append]
    refine ⟨hpw, hqr.tail, ?_⟩
    intro a ha z hz
    rw [hpl] at ha
    simp only [Option.mem_def, Option.some.injEq] at ha
    subst ha
    rw [hbr] at hz hqr
    simp only [List.tail_cons] at hz
    exact isWalk_junction hqr hz
  have hhead : (p ++ q.reverse.tail).head? = some x := by
    rw [List.head?_append_of_ne_nil p hpne]
    exact hph
  have hlast : (p ++ q.reverse.tail).getLast? = some x := by
    rw [hbr]
    simp only [List.tail_cons]
    cases hr : r with
    | nil =>
        rw [hbr, hr] at hqrl
        simp only [List.getLast?_singleton, Option.some.injEq] at hqrl
        subst hqrl
        simpa using hpl
    | cons c r' =>
        rw [List.getLast?_append_of_ne_nil p (by simp)]
        rw [hbr, hr] at hqrl
        simpa using hqrl
  have hclosed : S.IsClosedWalk x (p ++ q.reverse.tail) := ⟨hwalk, hhead, hlast⟩
  have hzero := crossings_eq_zero_of_closed hSC hχ hclosed
  have hglue := crossings_glue χ (l := p) (m := q.reverse) hpl (by rw [hbr]; rfl)
  rw [hglue, crossings_reverse hχ.symm] at hzero
  have h2 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  exact h2 _ _ hzero

/-! ### Walls are two-sided -/

/-- **Two-sidedness of walls.**  In a connected, simply connected square complex every
square-closed family of edges `χ` is the set of edges joining the two classes of a two-colouring
`σ` of the vertices: `σ u + σ v = χ u v` for every edge `u v`.  This is the combinatorial half of
Sageev's hyperplane construction: a hyperplane of a simply connected cube complex separates the
complex into two halfspaces. -/
theorem exists_side (hSC : S.SimplyConnected) {x₀ : Vx}
    (hconn : ∀ v : Vx, ∃ l, S.IsWalkFrom x₀ v l) {χ : Vx → Vx → ZMod 2} (hχ : S.IsWallLabel χ) :
    ∃ σ : Vx → ZMod 2, σ x₀ = 0 ∧ ∀ u v : Vx, S.adj u v → σ u + σ v = χ u v := by
  classical
  refine ⟨fun v => crossings χ (Classical.choose (hconn v)), ?_, ?_⟩
  · have hbase : S.IsWalkFrom x₀ x₀ [x₀] := ⟨List.isChain_singleton .., rfl, rfl⟩
    have := crossings_eq_of_walkFrom hSC hχ (Classical.choose_spec (hconn x₀)) hbase
    simpa using this
  · intro u v huv
    have hpspec : S.IsWalkFrom x₀ u (Classical.choose (hconn u)) := Classical.choose_spec (hconn u)
    obtain ⟨hpw, hph, hpl⟩ := hpspec
    set p := Classical.choose (hconn u) with hp
    have hpne : p ≠ [] := by intro h; rw [h] at hph; simp at hph
    -- extend the chosen walk to `u` by the edge `u v`
    have hext : S.IsWalkFrom x₀ v (p ++ [v]) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [IsWalk, List.isChain_append]
        refine ⟨hpw, List.isChain_singleton .., ?_⟩
        intro a ha z hz
        rw [hpl] at ha
        simp only [Option.mem_def, Option.some.injEq] at ha
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
        subst ha; subst hz
        exact huv
      · rw [List.head?_append_of_ne_nil p hpne]; exact hph
      · simp
    have hglue := crossings_glue χ (l := p) (m := [u, v]) hpl rfl
    simp only [List.tail_cons] at hglue
    have hcross : crossings χ (p ++ [v]) = crossings χ p + χ u v := by
      rw [hglue]; simp
    have hv := crossings_eq_of_walkFrom hSC hχ (Classical.choose_spec (hconn v)) hext
    have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
    show crossings χ p + crossings χ (Classical.choose (hconn v)) = χ u v
    rw [hv, hcross, ← add_assoc, h2, zero_add]

/-- With the wall label that is constantly `1` (the family of *all* edges): the one-skeleton of a
connected, simply connected square complex is bipartite. -/
theorem exists_bipartition (hSC : S.SimplyConnected) {x₀ : Vx}
    (hconn : ∀ v : Vx, ∃ l, S.IsWalkFrom x₀ v l) :
    ∃ σ : Vx → ZMod 2, ∀ u v : Vx, S.adj u v → σ u ≠ σ v := by
  obtain ⟨σ, -, hσ⟩ := exists_side hSC hconn (χ := fun _ _ => 1)
    ⟨fun _ _ => rfl, fun _ => rfl⟩
  refine ⟨σ, fun u v huv hne => ?_⟩
  have h := hσ u v huv
  rw [hne] at h
  have h2 : ∀ a : ZMod 2, a + a ≠ 1 := by decide
  exact h2 _ h

theorem crossings_one (a : Vx) : ∀ t : List Vx,
    crossings (fun _ _ => (1 : ZMod 2)) (a :: t) = (t.length : ZMod 2) := by
  intro t
  induction t generalizing a with
  | nil => simp
  | cons b t ih =>
      simp only [crossings_cons_cons, ih b, List.length_cons, Nat.cast_add, Nat.cast_one]
      ring

/-- Closed walks of a simply connected square complex have even length (their vertex list has odd
length): the one-skeleton has no odd cycles. -/
theorem closed_walk_length_odd (hSC : S.SimplyConnected) {x : Vx} {l : List Vx}
    (hl : S.IsClosedWalk x l) : (l.length : ZMod 2) = 1 := by
  have hwall : S.IsWallLabel (fun _ _ => (1 : ZMod 2)) := ⟨fun _ _ => rfl, fun _ => rfl⟩
  have hzero := crossings_eq_zero_of_closed hSC hwall hl
  obtain ⟨a, t, rfl⟩ : ∃ a t, l = a :: t := by
    cases l with
    | nil => exact absurd hl.2.1 (by simp)
    | cons a t => exact ⟨a, t, rfl⟩
  rw [crossings_one] at hzero
  simp only [List.length_cons, Nat.cast_add, Nat.cast_one, hzero, zero_add]

/-! ### Edges lying in no square -/

/-- `IsEdgePair u v x y` says that `{x, y}` is the edge `{u, v}`. -/
def IsEdgePair (u v x y : Vx) : Prop := (x = u ∧ y = v) ∨ (x = v ∧ y = u)

/-- **An edge lying in no square separates the complex.**  There is a two-colouring of the vertices
under which the two endpoints of such an edge get different colours while all other edges are
monochromatic; in particular every walk between its endpoints uses the edge. -/
theorem exists_side_edge (hSC : S.SimplyConnected) {x₀ : Vx}
    (hconn : ∀ v : Vx, ∃ l, S.IsWalkFrom x₀ v l) {u v : Vx} (huv : S.adj u v)
    (hns : ∀ a b c d : Vx, S.sq a b c d → ¬ IsEdgePair u v a b) :
    ∃ σ : Vx → ZMod 2, σ u ≠ σ v ∧
      ∀ a b : Vx, S.adj a b → ¬ IsEdgePair u v a b → σ a = σ b := by
  classical
  have hflip : ∀ a b : Vx, IsEdgePair u v a b ↔ IsEdgePair u v b a := by
    intro a b; unfold IsEdgePair; tauto
  have hwall : S.IsWallLabel (fun a b => if IsEdgePair u v a b then (1 : ZMod 2) else 0) := by
    constructor
    · intro a b
      by_cases h : IsEdgePair u v a b
      · simp only [if_pos h, if_pos ((hflip a b).mp h)]
      · simp only [if_neg h, if_neg (fun hc => h ((hflip a b).mpr hc))]
    · intro a b c d hsq
      have h1 : ¬ IsEdgePair u v a b := hns _ _ _ _ hsq
      have h2 : ¬ IsEdgePair u v c d := hns _ _ _ _ (S.sq_rotate (S.sq_rotate hsq))
      simp only [if_neg h1, if_neg h2]
  obtain ⟨σ, -, hσ⟩ := exists_side hSC hconn hwall
  refine ⟨σ, ?_, ?_⟩
  · have h := hσ u v huv
    have hedge : IsEdgePair u v u v := Or.inl ⟨rfl, rfl⟩
    simp only [if_pos hedge] at h
    intro hcon
    rw [hcon] at h
    have h2 : ∀ a : ZMod 2, a + a ≠ 1 := by decide
    exact h2 _ h
  · intro a b hab hnot
    have h := hσ a b hab
    simp only [if_neg hnot] at h
    have h2 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
    exact h2 _ _ h

/-- **Every triangle of a connected, simply connected square complex has a side lying in a
square.**  (In the cube complexes of the paper the links are flag and at most two-dimensional, so no
square may contain a side of a triangle; the statement then says that there are no triangles, as
must be the case for a median graph.) -/
theorem triangle_side_in_square (hSC : S.SimplyConnected) {x₀ : Vx}
    (hconn : ∀ v : Vx, ∃ l, S.IsWalkFrom x₀ v l) {a b c : Vx} (hab : S.adj a b) (hbc : S.adj b c)
    (hca : S.adj c a) :
    ∃ p q r s : Vx, S.sq p q r s ∧
      (IsEdgePair a b p q ∨ IsEdgePair b c p q ∨ IsEdgePair c a p q) := by
  by_contra hcon
  push_neg at hcon
  have hns : ∀ p q r s : Vx, S.sq p q r s → ¬ IsEdgePair a b p q := by
    intro p q r s hsq
    exact (hcon p q r s hsq).1
  obtain ⟨σ, hne, hmono⟩ := exists_side_edge hSC hconn hab hns
  have hbne : b ≠ c := by rintro rfl; exact S.adj_irrefl b hbc
  have hcne : c ≠ a := by rintro rfl; exact S.adj_irrefl c hca
  have hane : a ≠ b := by rintro rfl; exact S.adj_irrefl a hab
  have h1 : σ b = σ c := by
    refine hmono b c hbc ?_
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hane h1.symm
    · exact hcne h2
  have h2 : σ c = σ a := by
    refine hmono c a hca ?_
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hcne h1
    · exact hbne h1.symm
  exact hne (by rw [← h2, ← h1])

/-! ### Wall systems and halfspace (Roller) coordinates

A *wall system* records the hyperplanes of the complex: a family of square-closed edge labels such
that every edge crosses exactly one of them.  In a connected, simply connected complex each wall is
two-sided by `SquareComplex.exists_side`, so every vertex `v` acquires the set of walls separating
it from the base vertex; it is finite, it is empty at the base vertex, and along an edge it changes
by exactly one wall.  These are precisely the coordinates on which `FiniteChains.RollerModel` is
built. -/

/-- A **wall system** on a square complex: a family `χ i` of square-closed edge labels (the
hyperplanes) such that each edge crosses exactly one of them. -/
structure WallSystem (S : SquareComplex Vx) (ι : Type*) where
  /-- The characteristic function of the `i`-th wall. -/
  χ : ι → Vx → Vx → ZMod 2
  /-- Each member of the family is square-closed and symmetric. -/
  isWall : ∀ i, S.IsWallLabel (χ i)
  /-- Every edge crosses exactly one wall. -/
  edge_unique : ∀ u v : Vx, S.adj u v → ∃! i : ι, χ i u v = 1

theorem isChain_zip_tail {R : Vx → Vx → Prop} :
    ∀ {l : List Vx}, List.IsChain R l → ∀ p ∈ l.zip l.tail, R p.1 p.2 := by
  intro l
  induction l with
  | nil => intro _ p hp; simp at hp
  | cons a t ih =>
      intro h p hp
      match t with
      | [] => simp at hp
      | b :: t' =>
          rw [List.isChain_cons_cons] at h
          simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact h.1
          · exact ih h.2 p (by simpa using hp)

/-- If a wall separates the two endpoints of a walk, then the walk crosses it along one of its
edges. -/
theorem exists_crossing_pair {χ : Vx → Vx → ZMod 2} {σ : Vx → ZMod 2}
    (hσ : ∀ u v : Vx, S.adj u v → σ u + σ v = χ u v) :
    ∀ {l : List Vx} {x y : Vx}, S.IsWalkFrom x y l → σ x ≠ σ y →
      ∃ p ∈ l.zip l.tail, χ p.1 p.2 = 1 := by
  intro l
  induction l with
  | nil => intro x y hw _; exact absurd hw.2.1 (by simp)
  | cons a t ih =>
      intro x y hw hne
      have hax : a = x := by simpa using hw.2.1
      subst hax
      match t with
      | [] =>
          exfalso
          have : a = y := by simpa using hw.2.2
          exact hne (by rw [this])
      | b :: t' =>
          have hchain := hw.1
          have hab : S.adj a b := (List.isChain_cons_cons.mp hchain).1
          by_cases hchi : χ a b = 1
          · exact ⟨(a, b), by simp, hchi⟩
          · have hsum := hσ a b hab
            have hzero : χ a b = 0 := by
              have hz : ∀ c : ZMod 2, c ≠ 1 → c = 0 := by decide
              exact hz _ hchi
            have hab' : σ a = σ b := by
              have h2 : ∀ c d : ZMod 2, c + d = 0 → c = d := by decide
              exact h2 _ _ (by rw [hsum, hzero])
            have hsub : S.IsWalkFrom b y (b :: t') :=
              ⟨(List.isChain_cons_cons.mp hchain).2, rfl, by simpa using hw.2.2⟩
            obtain ⟨p, hp, hpc⟩ := ih hsub (by rw [← hab']; exact hne)
            refine ⟨p, ?_, hpc⟩
            simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
            exact Or.inr hp

/-- The set of walls crossed by a walk is finite: each of its edges crosses exactly one wall. -/
theorem wallsOf_finite {ι : Type*} (W : S.WallSystem ι) {l : List Vx} (hl : S.IsWalk l) :
    {i : ι | ∃ p ∈ l.zip l.tail, W.χ i p.1 p.2 = 1}.Finite := by
  classical
  have hsub : {i : ι | ∃ p ∈ l.zip l.tail, W.χ i p.1 p.2 = 1} ⊆
      ⋃ p ∈ (l.zip l.tail), {i : ι | W.χ i p.1 p.2 = 1} := by
    intro i hi
    obtain ⟨p, hp, hpc⟩ := hi
    exact Set.mem_biUnion hp hpc
  refine Set.Finite.subset (Set.Finite.biUnion (l.zip l.tail).finite_toSet ?_) hsub
  intro p hp
  have hadj : S.adj p.1 p.2 := isChain_zip_tail hl p (by simpa using hp)
  obtain ⟨j, -, hj⟩ := W.edge_unique p.1 p.2 hadj
  refine Set.Subsingleton.finite ?_
  intro i hi i' hi'
  rw [hj i hi, hj i' hi']

/-- **Halfspace (Roller) coordinates.**  In a connected, simply connected square complex carrying a
wall system there is, for every wall, a partition of the vertices into its two sides; the set of
walls separating a vertex from the base vertex is finite, it is empty at the base vertex, and along
an edge it changes by exactly one wall — the wall that the edge crosses. -/
theorem exists_rollerCoordinates {ι : Type*} (hSC : S.SimplyConnected) {x₀ : Vx}
    (hconn : ∀ v : Vx, ∃ l, S.IsWalkFrom x₀ v l) (W : S.WallSystem ι) :
    ∃ σ : ι → Vx → ZMod 2,
      (∀ i, σ i x₀ = 0) ∧
      (∀ (i : ι) (u v : Vx), S.adj u v → σ i u + σ i v = W.χ i u v) ∧
      (∀ v : Vx, {i : ι | σ i v ≠ σ i x₀}.Finite) ∧
      (∀ u v : Vx, S.adj u v → ∃ j : ι, {i : ι | σ i u ≠ σ i v} = {j}) := by
  classical
  choose σ hbase hside using fun i : ι => exists_side hSC hconn (W.isWall i)
  refine ⟨σ, hbase, fun i => hside i, ?_, ?_⟩
  · intro v
    obtain ⟨l, hl⟩ := hconn v
    have hsub : {i : ι | σ i v ≠ σ i x₀} ⊆ {i : ι | ∃ p ∈ l.zip l.tail, W.χ i p.1 p.2 = 1} := by
      intro i hi
      exact exists_crossing_pair (hside i) hl (Ne.symm hi)
    exact Set.Finite.subset (wallsOf_finite W hl.1) hsub
  · intro u v huv
    obtain ⟨j, hj, hjuniq⟩ := W.edge_unique u v huv
    refine ⟨j, ?_⟩
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hi
      refine hjuniq i ?_
      have h := hside i u v huv
      have h2 : ∀ c d : ZMod 2, c ≠ d → c + d = 1 := by decide
      show W.χ i u v = 1
      rw [← h]
      exact h2 _ _ hi
    · intro hij
      subst hij
      have h := hside i u v huv
      intro hcon
      rw [hcon, hj] at h
      have h2 : ∀ c : ZMod 2, c + c ≠ 1 := by decide
      exact h2 _ h

/-- The set of walls separating any two vertices is finite: the wall pseudometric of a connected,
simply connected square complex with a wall system is well defined. -/
theorem separating_finite {ι : Type*} {σ : ι → Vx → ZMod 2} {x₀ : Vx}
    (hfin : ∀ v : Vx, {i : ι | σ i v ≠ σ i x₀}.Finite) (u v : Vx) :
    {i : ι | σ i u ≠ σ i v}.Finite := by
  refine Set.Finite.subset ((hfin u).union (hfin v)) ?_
  intro i hi
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
  exact hi (by rw [hcon.1, hcon.2])

end SquareComplex

end FiniteChains
