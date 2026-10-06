import RequestProject.SquareComplexCovering
import RequestProject.SquareComplexTreeCase

/-!
# The combinatorial fundamental group of a square complex

This file introduces the edge-path group of a square complex: closed walks based at a vertex,
taken up to the homotopy through walks of
`RequestProject/SquareComplexWalkHomotopy.lean`.

* `FiniteChains.SquareComplex.Pi1` — the group of homotopy classes of closed walks;
* `FiniteChains.SquareComplex.pi1_trivial_iff_simplyConnectedW` — the complex is simply
  connected exactly when this group is trivial;
* `FiniteChains.SquareComplex.IsCovering.liftEnd` — the end point of the lift of a walk of the
  base, and `FiniteChains.SquareComplex.IsCovering.monodromy` — the resulting **monodromy map**
  from `Pi1` of the base to the fibre, which is a bijection as soon as the covering complex is
  connected and simply connected.

Walks are taken in the form of `SimpleGraph.Walk` of the one-skeleton `toSimpleGraph`, so that
concatenation, reversal and their algebraic identities are available; homotopy is compared with
them through `SimpleGraph.Walk.support`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

namespace SquareComplex

universe u v

variable {Vx : Type u} {S : SquareComplex Vx}

/-! ### Walks as lists and as `SimpleGraph.Walk`s -/

/-- The support of a walk of the one-skeleton is a walk from its initial to its terminal
vertex. -/
theorem isWalkFrom_support' {x y : Vx} (w : (toSimpleGraph S).Walk x y) :
    S.IsWalkFrom x y w.support :=
  isWalkFrom_support (fun _ _ h => h) w

theorem isWalk_support {x y : Vx} (w : (toSimpleGraph S).Walk x y) : S.IsWalk w.support :=
  (isWalkFrom_support' w).1

/-- Every walk given as a list of vertices is the support of a walk of the one-skeleton. -/
theorem exists_walk_of_isWalkFrom : ∀ {l : List Vx} {x y : Vx}, S.IsWalkFrom x y l →
    ∃ w : (toSimpleGraph S).Walk x y, w.support = l := by
  intro l
  induction l with
  | nil => intro x y h; simp [IsWalkFrom] at h
  | cons a t ih =>
      intro x y h
      obtain ⟨hw, hh, hl⟩ := h
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      cases t with
      | nil =>
          have hay : a = y := by simpa using hl
          subst hay
          exact ⟨SimpleGraph.Walk.nil, by simp⟩
      | cons b s =>
          rw [IsWalk, List.isChain_cons_cons] at hw
          have hlast : (b :: s).getLast? = some y := by simpa using hl
          obtain ⟨w, hwsupp⟩ := ih (x := b) (y := y) ⟨hw.2, rfl, hlast⟩
          refine ⟨SimpleGraph.Walk.cons hw.1 w, ?_⟩
          rw [SimpleGraph.Walk.support_cons, hwsupp]

/-! ### Appending a fixed walk to a homotopy -/

theorem Move.append_right {l l' : List Vx} (h : S.Move l l') (t : List Vx) :
    S.Move (l ++ t) (l' ++ t) := by
  induction h with
  | backtrack x y q => exact Move.backtrack x y (q ++ t)
  | square hsq q => exact Move.square hsq (q ++ t)
  | cons x _ ih => exact Move.cons x ih

theorem isWalk_append {l t : List Vx} (hl : S.IsWalk l) (ht : S.IsWalk t)
    (hj : ∀ a ∈ l.getLast?, ∀ b ∈ t.head?, S.adj a b) : S.IsWalk (l ++ t) := by
  rw [IsWalk, List.isChain_append]
  exact ⟨hl, ht, hj⟩

/-- A homotopy through walks may be followed by a fixed walk. -/
theorem WalkHomotopic.append_right {l l' t : List Vx} (h : S.WalkHomotopic l l')
    (ht : S.IsWalk t)
    (hj : ∀ a ∈ l.getLast?, ∀ b ∈ t.head?, S.adj a b) :
    S.WalkHomotopic (l ++ t) (l' ++ t) := by
  induction h with
  | refl => exact WalkHomotopic.refl _
  | @tail m m' hlm hstep ih =>
      have hlm' : S.WalkHomotopic l m := hlm
      have hlast : l.getLast? = m.getLast? := hlm'.getLast?_eq
      refine (ih).trans (WalkHomotopic.of_walkMove ?_)
      have hjm : ∀ a ∈ m.getLast?, ∀ b ∈ t.head?, S.adj a b := by
        rw [← hlast]; exact hj
      have hlast' : m.getLast? = m'.getLast? := by
        rcases hstep with ⟨hmove, -⟩ | ⟨hmove, -⟩
        · exact hmove.getLast?_eq
        · exact hmove.getLast?_eq.symm
      have hjm' : ∀ a ∈ m'.getLast?, ∀ b ∈ t.head?, S.adj a b := by
        rw [← hlast']; exact hjm
      rcases hstep with ⟨hmove, hw⟩ | ⟨hmove, hw⟩
      · exact Or.inl ⟨hmove.append_right t, isWalk_append hw ht hjm⟩
      · exact Or.inr ⟨hmove.append_right t, isWalk_append hw ht hjm'⟩

/-! ### Homotopy of `SimpleGraph.Walk`s -/

/-- Homotopy, through walks, of two walks of the one-skeleton with the same end points. -/
def WalkHtpy (S : SquareComplex Vx) {x y : Vx} (p q : (toSimpleGraph S).Walk x y) : Prop :=
  S.WalkHomotopic p.support q.support

namespace WalkHtpy

variable {x y : Vx}

theorem refl (p : (toSimpleGraph S).Walk x y) : S.WalkHtpy p p := WalkHomotopic.refl _

theorem symm {p q : (toSimpleGraph S).Walk x y} (h : S.WalkHtpy p q) : S.WalkHtpy q p :=
  WalkHomotopic.symm h

theorem trans {p q r : (toSimpleGraph S).Walk x y} (h : S.WalkHtpy p q) (h' : S.WalkHtpy q r) :
    S.WalkHtpy p r := WalkHomotopic.trans h h'

end WalkHtpy

/-- Homotopies may be prefixed by a fixed walk. -/
theorem walkHtpy_append_left {a b c : Vx} (u : (toSimpleGraph S).Walk a b)
    {p q : (toSimpleGraph S).Walk b c} (h : S.WalkHtpy p q) :
    S.WalkHtpy (u.append p) (u.append q) := by
  induction u with
  | nil => simpa [SimpleGraph.Walk.nil_append] using h
  | @cons a' b' c' hadj r ih =>
      rw [WalkHtpy, SimpleGraph.Walk.cons_append, SimpleGraph.Walk.cons_append,
        SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons]
      refine WalkHomotopic.cons ?_ (ih h)
      intro z hz
      rw [SimpleGraph.Walk.support_eq_cons] at hz
      simp only [List.head?_cons, Option.some.injEq] at hz
      subst hz
      exact hadj

/-- Homotopies may be followed by a fixed walk. -/
theorem walkHtpy_append_right {a b c : Vx} {p q : (toSimpleGraph S).Walk a b}
    (h : S.WalkHtpy p q) (v : (toSimpleGraph S).Walk b c) :
    S.WalkHtpy (p.append v) (q.append v) := by
  rw [WalkHtpy, SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_append]
  refine WalkHomotopic.append_right h ((isWalk_support v).tail) ?_
  intro a' ha' b' hb'
  have hlast : p.support.getLast? = some b := (isWalkFrom_support' p).2.2
  rw [hlast] at ha'
  simp only [Option.mem_def, Option.some.injEq] at ha'
  subst ha'
  have hv : S.IsWalk v.support := isWalk_support v
  rw [SimpleGraph.Walk.support_eq_cons v] at hv
  exact isWalk_junction hv hb'

/-! ### Reversing a homotopy -/

theorem Move.append_left {l l' : List Vx} (h : S.Move l l') (pre : List Vx) :
    S.Move (pre ++ l) (pre ++ l') := by
  induction pre with
  | nil => simpa using h
  | cons a t ih => exact Move.cons a ih

theorem Move.reverse {l l' : List Vx} (h : S.Move l l') : S.Move l.reverse l'.reverse := by
  induction h with
  | backtrack x y q =>
      have h0 : S.Move [x, y, x] [x] := Move.backtrack x y []
      have := h0.append_left q.reverse
      simpa using this
  | @square a b c d hsq q =>
      have hsq' : S.sq c b a d := S.sq_rotate (S.sq_reverse hsq)
      have h0 : S.Move [c, b, a] [c, d, a] := Move.square hsq' []
      have := h0.append_left q.reverse
      simpa using this
  | cons x _ ih =>
      have := ih.append_right [x]
      simpa using this

theorem WalkMove.reverse {l l' : List Vx} (h : S.WalkMove l l') :
    S.WalkMove l.reverse l'.reverse := by
  rcases h with ⟨hm, hw⟩ | ⟨hm, hw⟩
  · exact Or.inl ⟨hm.reverse, isWalk_reverse hw⟩
  · exact Or.inr ⟨hm.reverse, isWalk_reverse hw⟩

theorem WalkHomotopic.reverse {l l' : List Vx} (h : S.WalkHomotopic l l') :
    S.WalkHomotopic l.reverse l'.reverse := by
  induction h with
  | refl => exact WalkHomotopic.refl _
  | tail _ hstep ih => exact ih.trans (WalkHomotopic.of_walkMove hstep.reverse)

/-- Reversing a homotopy of walks of the one-skeleton. -/
theorem walkHtpy_reverse {a b : Vx} {p q : (toSimpleGraph S).Walk a b} (h : S.WalkHtpy p q) :
    S.WalkHtpy p.reverse q.reverse := by
  rw [WalkHtpy, SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_reverse]
  exact WalkHomotopic.reverse h

/-! ### A walk followed by its reverse contracts -/

/-- **A walk followed by its reverse is contractible**: it is homotopic, through walks, to the
constant walk at its initial vertex. -/
theorem walkHtpy_append_reverse : ∀ {a b : Vx} (p : (toSimpleGraph S).Walk a b),
    S.WalkHtpy (p.append p.reverse) SimpleGraph.Walk.nil := by
  intro a b p
  induction p with
  | nil => exact WalkHomotopic.refl _
  | @cons a' c' b' hadj q ih =>
      have hrw : (SimpleGraph.Walk.cons hadj q).append (SimpleGraph.Walk.cons hadj q).reverse
          = SimpleGraph.Walk.cons hadj
              ((q.append q.reverse).append
                (SimpleGraph.Walk.cons hadj.symm SimpleGraph.Walk.nil)) := by
        rw [SimpleGraph.Walk.reverse_cons, SimpleGraph.Walk.cons_append,
          SimpleGraph.Walk.append_assoc]
      have hstep : S.WalkHtpy ((q.append q.reverse).append
            (SimpleGraph.Walk.cons hadj.symm SimpleGraph.Walk.nil))
          (SimpleGraph.Walk.nil.append
            (SimpleGraph.Walk.cons hadj.symm SimpleGraph.Walk.nil)) :=
        walkHtpy_append_right ih _
      have hsupp : S.WalkHomotopic ((q.append q.reverse).append
            (SimpleGraph.Walk.cons hadj.symm SimpleGraph.Walk.nil)).support [c', a'] := by
        refine WalkHomotopic.trans hstep ?_
        simp only [SimpleGraph.Walk.nil_append, SimpleGraph.Walk.support_cons,
          SimpleGraph.Walk.support_nil]
        exact WalkHomotopic.refl _
      have hcons : S.WalkHomotopic (a' :: ((q.append q.reverse).append
            (SimpleGraph.Walk.cons hadj.symm SimpleGraph.Walk.nil)).support) [a', c', a'] := by
        refine WalkHomotopic.cons ?_ hsupp
        intro z hz
        rw [SimpleGraph.Walk.support_eq_cons] at hz
        simp only [List.head?_cons, Option.some.injEq] at hz
        subst hz
        exact hadj
      have hback : S.WalkMove [a', c', a'] [a'] := by
        refine Or.inl ⟨Move.backtrack a' c' [], ?_⟩
        rw [IsWalk, List.isChain_cons_cons, List.isChain_cons_cons]
        exact ⟨hadj, S.adj_symm hadj, by simp⟩
      rw [WalkHtpy, hrw, SimpleGraph.Walk.support_cons]
      refine hcons.trans ?_
      simpa using WalkHomotopic.of_walkMove hback

/-! ### The boundary of a square contracts -/

/-- **The boundary of a two-cell is contractible**: the closed walk running once around a square
is homotopic, through walks, to its base point. -/
theorem walkHomotopic_sq_boundary {a b c d : Vx} (h : S.sq a b c d) :
    S.WalkHomotopic [a, b, c, d, a] [a] := by
  obtain ⟨hab, hbc, hcd, hda⟩ := S.sq_adj h
  have hw1 : S.IsWalk [a, b, c, d, a] := by
    rw [IsWalk]
    simp only [List.isChain_cons_cons]
    exact ⟨hab, hbc, hcd, hda, by simp⟩
  have hw2 : S.IsWalk [a, d, c, d, a] := by
    rw [IsWalk]
    simp only [List.isChain_cons_cons]
    exact ⟨S.adj_symm hda, S.adj_symm hcd, hcd, hda, by simp⟩
  have hw3 : S.IsWalk [a, d, a] := by
    rw [IsWalk]
    simp only [List.isChain_cons_cons]
    exact ⟨S.adj_symm hda, hda, by simp⟩
  have m1 : S.WalkMove [a, b, c, d, a] [a, d, c, d, a] :=
    Or.inl ⟨Move.square h [d, a], hw1⟩
  have m2 : S.WalkMove [a, d, c, d, a] [a, d, a] :=
    Or.inl ⟨Move.cons a (Move.backtrack d c [a]), hw2⟩
  have m3 : S.WalkMove [a, d, a] [a] :=
    Or.inl ⟨Move.backtrack a d [], hw3⟩
  exact ((WalkHomotopic.of_walkMove m1).trans (WalkHomotopic.of_walkMove m2)).trans
    (WalkHomotopic.of_walkMove m3)

/-! ### The fundamental group -/

/-- Homotopy through walks, as a setoid on the walks from `x` to `y`. -/
def walkSetoid (S : SquareComplex Vx) (x y : Vx) : Setoid ((toSimpleGraph S).Walk x y) where
  r p q := S.WalkHtpy p q
  iseqv := ⟨fun p => WalkHtpy.refl p, fun h => WalkHtpy.symm h, fun h h' => WalkHtpy.trans h h'⟩

/-- **The combinatorial fundamental group** (edge-path group) of a square complex: closed walks
based at `x`, up to homotopy through walks. -/
def Pi1 (S : SquareComplex Vx) (x : Vx) : Type u := Quotient (walkSetoid S x x)

namespace Pi1

variable {x : Vx}

/-- The class of a closed walk. -/
def mk (p : (toSimpleGraph S).Walk x x) : S.Pi1 x := Quotient.mk (walkSetoid S x x) p

theorem mk_eq_mk {p q : (toSimpleGraph S).Walk x x} : mk p = mk q ↔ S.WalkHtpy p q :=
  Quotient.eq (r := walkSetoid S x x)

instance : Group (S.Pi1 x) where
  mul :=
    Quotient.map₂ (fun p q => p.append q)
      (by
        intro p p' hp q q' hq
        exact WalkHtpy.trans (walkHtpy_append_right hp q) (walkHtpy_append_left p' hq))
  one := mk SimpleGraph.Walk.nil
  inv :=
    Quotient.map (fun p => p.reverse) (by intro p q h; exact walkHtpy_reverse h)
  mul_assoc := by
    refine Quotient.ind fun p => Quotient.ind fun q => Quotient.ind fun r => ?_
    exact congrArg mk (SimpleGraph.Walk.append_assoc p q r).symm
  one_mul := by
    refine Quotient.ind fun p => ?_
    exact congrArg mk (SimpleGraph.Walk.nil_append p)
  mul_one := by
    refine Quotient.ind fun p => ?_
    exact congrArg mk (SimpleGraph.Walk.append_nil p)
  inv_mul_cancel := by
    refine Quotient.ind fun p => ?_
    refine mk_eq_mk.2 ?_
    have := walkHtpy_append_reverse p.reverse
    rwa [SimpleGraph.Walk.reverse_reverse] at this

theorem mul_mk (p q : (toSimpleGraph S).Walk x x) : mk p * mk q = mk (p.append q) := rfl

theorem one_eq : (1 : S.Pi1 x) = mk (SimpleGraph.Walk.nil (u := x)) := rfl

theorem inv_mk (p : (toSimpleGraph S).Walk x x) : (mk p)⁻¹ = mk p.reverse := rfl

end Pi1

/-- **The fundamental group detects simple connectivity**: it is trivial at every base point
exactly when the complex is simply connected through walks. -/
theorem pi1_trivial_iff_simplyConnectedW :
    (∀ (x : Vx) (g : S.Pi1 x), g = 1) ↔ S.SimplyConnectedW := by
  constructor
  · intro h x l hl
    obtain ⟨w, rfl⟩ := exists_walk_of_isWalkFrom hl
    have := h x (Pi1.mk w)
    have hw : S.WalkHtpy w SimpleGraph.Walk.nil := Pi1.mk_eq_mk.1 this
    simpa [WalkHtpy] using hw
  · intro h x g
    refine Quotient.inductionOn g fun p => ?_
    refine Pi1.mk_eq_mk.2 ?_
    have hcw : S.IsClosedWalk x p.support := isWalkFrom_support' p
    simpa [WalkHtpy] using h x p.support hcw

end SquareComplex

end FiniteChains
