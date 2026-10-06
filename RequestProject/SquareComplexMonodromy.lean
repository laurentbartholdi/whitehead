module

public import RequestProject.SquareComplexPi1

@[expose] public section

/-!
# Monodromy of a covering of square complexes

For a covering `p : T → B` of square complexes, lifting a walk of the base which starts at
`p x₀` gives a walk of `T` starting at `x₀`; its end point depends only on the homotopy class of
the walk.  This defines the **monodromy map**

`FiniteChains.SquareComplex.IsCovering.monodromy : B.Pi1 (p x₀) → Vt`,

which takes values in the fibre over `p x₀`.  The main theorem,
`FiniteChains.SquareComplex.IsCovering.monodromy_bijective`, says that for a connected and simply
connected covering complex the monodromy map is a bijection from the fundamental group of the
base onto the fibre — the combinatorial form of the classical identification
`π₁(B) ≅ p⁻¹(b₀)` for the universal covering.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

namespace SquareComplex

universe u v

variable {Vt : Type u} {Vb : Type v} {T : SquareComplex Vt} {B : SquareComplex Vb} {p : Vt → Vb}

namespace IsCovering

/-- The image of an elementary move is an elementary move. -/
theorem map_move (hp : IsCovering T B p) {l l' : List Vt} (h : T.Move l l') :
    B.Move (l.map p) (l'.map p) := by
  induction h with
  | backtrack x y q => exact Move.backtrack (p x) (p y) (q.map p)
  | square hsq q => exact Move.square (hp.map_sq hsq) (q.map p)
  | cons x _ ih => exact Move.cons (p x) ih

theorem map_walkMove (hp : IsCovering T B p) {l l' : List Vt} (h : T.WalkMove l l') :
    B.WalkMove (l.map p) (l'.map p) := by
  rcases h with ⟨hm, hw⟩ | ⟨hm, hw⟩
  · exact Or.inl ⟨hp.map_move hm, hp.map_isWalk hw⟩
  · exact Or.inr ⟨hp.map_move hm, hp.map_isWalk hw⟩

/-- The image of a homotopy through walks is a homotopy through walks. -/
theorem map_walkHomotopic (hp : IsCovering T B p) {l l' : List Vt} (h : T.WalkHomotopic l l') :
    B.WalkHomotopic (l.map p) (l'.map p) := by
  induction h with
  | refl => exact WalkHomotopic.refl _
  | tail _ hstep ih => exact ih.trans (WalkHomotopic.of_walkMove (hp.map_walkMove hstep))

open Classical in
/-- The end point of the unique lift, issuing from `x`, of the edge from `p x` to `w`
(junk value `x` when `p x` and `w` are not joined by an edge). -/
noncomputable def edgeLift (hp : IsCovering T B p) (x : Vt) (w : Vb) : Vt :=
  if h : B.adj (p x) w then (hp.lift_adj x h).exists.choose else x

theorem edgeLift_spec (hp : IsCovering T B p) {x : Vt} {w : Vb} (h : B.adj (p x) w) :
    T.adj x (hp.edgeLift x w) ∧ p (hp.edgeLift x w) = w := by
  classical
  rw [edgeLift, dif_pos h]
  exact (hp.lift_adj x h).exists.choose_spec

/-- The end point of the lift, issuing from `x`, of a walk of the base. -/
noncomputable def liftEnd (hp : IsCovering T B p) :
    ∀ {b c : Vb}, (toSimpleGraph B).Walk b c → Vt → Vt
  | _, _, SimpleGraph.Walk.nil => fun x => x
  | _, _, @SimpleGraph.Walk.cons _ _ _ v _ _ q => fun x => hp.liftEnd q (hp.edgeLift x v)

@[simp] theorem liftEnd_nil (hp : IsCovering T B p) (b : Vb) (x : Vt) :
    hp.liftEnd (SimpleGraph.Walk.nil (u := b)) x = x := rfl

@[simp] theorem liftEnd_cons (hp : IsCovering T B p) {b v c : Vb}
    (h : (toSimpleGraph B).Adj b v) (q : (toSimpleGraph B).Walk v c) (x : Vt) :
    hp.liftEnd (SimpleGraph.Walk.cons h q) x = hp.liftEnd q (hp.edgeLift x v) := rfl

/-- **The lift exists**: over any walk of the base issuing from `p x` there is a walk of `T`
issuing from `x` and ending at `liftEnd`. -/
theorem liftEnd_spec (hp : IsCovering T B p) : ∀ {b c : Vb} (w : (toSimpleGraph B).Walk b c)
    (x : Vt), p x = b →
    ∃ lt : List Vt, T.IsWalk lt ∧ lt.head? = some x ∧ lt.getLast? = some (hp.liftEnd w x) ∧
      lt.map p = w.support := by
  intro b c w
  induction w with
  | nil =>
      intro x hx
      exact ⟨[x], by simp [IsWalk], by simp, by simp, by simp [hx]⟩
  | @cons b' v c' hadj q ih =>
      intro x hx
      have hadj' : B.adj (p x) v := by rw [hx]; exact hadj
      obtain ⟨hxy, hpy⟩ := hp.edgeLift_spec hadj'
      obtain ⟨lt, hw, hh, hlast, hmap⟩ := ih (hp.edgeLift x v) hpy
      have hne : lt ≠ [] := by
        intro hnil; rw [hnil] at hh; simp at hh
      refine ⟨x :: lt, isWalk_cons hw ?_, by simp, ?_, ?_⟩
      · intro y hy
        rw [hh] at hy
        simp only [Option.some.injEq] at hy
        subst hy
        exact hxy
      · cases hlt : lt with
        | nil => exact absurd hlt hne
        | cons a t =>
            rw [hlt] at hlast
            rw [List.getLast?_cons_cons]
            exact hlast
      · rw [List.map_cons, hmap, hx, SimpleGraph.Walk.support_cons]

/-- **Uniqueness of the lift**: any walk of `T` lying over `w` and issuing from `x` ends at
`liftEnd`. -/
theorem liftEnd_eq_of_lift (hp : IsCovering T B p) {b c : Vb} (w : (toSimpleGraph B).Walk b c)
    {x : Vt} {lt : List Vt} (hw : T.IsWalk lt) (hh : lt.head? = some x)
    (hmap : lt.map p = w.support) : lt.getLast? = some (hp.liftEnd w x) := by
  have hx : p x = b := by
    have h1 : (lt.map p).head? = some (p x) := by rw [List.head?_map, hh]; rfl
    rw [hmap, SimpleGraph.Walk.support_eq_cons] at h1
    cases w <;> simpa using h1.symm
  obtain ⟨lt', hw', hh', hlast', hmap'⟩ := hp.liftEnd_spec w x hx
  have : lt = lt' := hp.lift_unique hw hw' (by rw [hh, hh']) (by rw [hmap, hmap'])
  rw [this]
  exact hlast'

/-- The lift of a walk of the base stays in the fibres: it ends over the end point. -/
theorem p_liftEnd (hp : IsCovering T B p) {b c : Vb} (w : (toSimpleGraph B).Walk b c) {x : Vt}
    (hx : p x = b) : p (hp.liftEnd w x) = c := by
  obtain ⟨lt, hw, hh, hlast, hmap⟩ := hp.liftEnd_spec w x hx
  have h1 : (lt.map p).getLast? = some (p (hp.liftEnd w x)) := by
    rw [List.getLast?_map, hlast]; rfl
  rw [hmap] at h1
  have h2 : w.support.getLast? = some c := (isWalkFrom_support' w).2.2
  rw [h2] at h1
  simpa [SimpleGraph.Walk.head_support] using h1.symm

/-- Lifting a concatenation. -/
theorem liftEnd_append (hp : IsCovering T B p) : ∀ {a b c : Vb} (u : (toSimpleGraph B).Walk a b)
    (v : (toSimpleGraph B).Walk b c) (x : Vt),
    hp.liftEnd (u.append v) x = hp.liftEnd v (hp.liftEnd u x) := by
  intro a b c u
  induction u with
  | nil => intro v x; rfl
  | @cons a' w' b' hadj q ih =>
      intro v x
      rw [SimpleGraph.Walk.cons_append, liftEnd_cons, liftEnd_cons, ih]

/-- Lifting the reverse of a walk returns to the initial point. -/
theorem liftEnd_reverse (hp : IsCovering T B p) {b c : Vb} (w : (toSimpleGraph B).Walk b c)
    {x : Vt} (hx : p x = b) : hp.liftEnd w.reverse (hp.liftEnd w x) = x := by
  obtain ⟨lt, hw, hh, hlast, hmap⟩ := hp.liftEnd_spec w x hx
  have hrev : lt.reverse.getLast? = some (hp.liftEnd w.reverse (hp.liftEnd w x)) := by
    refine hp.liftEnd_eq_of_lift w.reverse (isWalk_reverse hw) ?_ ?_
    · rw [List.head?_reverse, hlast]
    · rw [List.map_reverse, hmap, SimpleGraph.Walk.support_reverse]
  rw [List.getLast?_reverse, hh] at hrev
  simpa using hrev.symm

/-- **Homotopy invariance**: homotopic walks of the base have lifts with the same end point. -/
theorem liftEnd_congr (hp : IsCovering T B p) {b c : Vb} {w w' : (toSimpleGraph B).Walk b c}
    (h : B.WalkHtpy w w') {x : Vt} (hx : p x = b) : hp.liftEnd w x = hp.liftEnd w' x := by
  obtain ⟨lt, hw, hh, hlast, hmap⟩ := hp.liftEnd_spec w x hx
  obtain ⟨lt', hw', hh', hmap', hhom⟩ := hp.lift_walkHomotopic h hw hmap
  have h1 : lt'.getLast? = some (hp.liftEnd w' x) :=
    hp.liftEnd_eq_of_lift w' hw' (by rw [hh', hh]) hmap'
  have h2 : lt.getLast? = lt'.getLast? := hhom.getLast?_eq
  rw [hlast, h1] at h2
  simpa using h2

/-! ### The monodromy map -/

/-- **The monodromy map**: the class of a closed walk of the base at `p x₀` goes to the end point
of its lift issuing from `x₀`. -/
noncomputable def monodromy (hp : IsCovering T B p) (x₀ : Vt) : B.Pi1 (p x₀) → Vt :=
  Quotient.lift (fun w => hp.liftEnd w x₀) (fun _ _ h => hp.liftEnd_congr h rfl)

@[simp] theorem monodromy_mk (hp : IsCovering T B p) (x₀ : Vt)
    (w : (toSimpleGraph B).Walk (p x₀) (p x₀)) :
    hp.monodromy x₀ (Pi1.mk w) = hp.liftEnd w x₀ := rfl

theorem monodromy_mem_fibre (hp : IsCovering T B p) (x₀ : Vt) (g : B.Pi1 (p x₀)) :
    p (hp.monodromy x₀ g) = p x₀ := by
  refine Quotient.inductionOn g fun w => ?_
  exact hp.p_liftEnd w rfl

@[simp] theorem monodromy_one (hp : IsCovering T B p) (x₀ : Vt) :
    hp.monodromy x₀ 1 = x₀ := rfl

/-- **Injectivity of the monodromy** for a simply connected covering complex. -/
theorem monodromy_injective (hp : IsCovering T B p) (hT : T.SimplyConnectedW) (x₀ : Vt) :
    Function.Injective (hp.monodromy x₀) := by
  have key : ∀ w : (toSimpleGraph B).Walk (p x₀) (p x₀), hp.liftEnd w x₀ = x₀ →
      Pi1.mk w = (1 : B.Pi1 (p x₀)) := by
    intro w hw
    obtain ⟨lt, hwt, hh, hlast, hmap⟩ := hp.liftEnd_spec w x₀ rfl
    rw [hw] at hlast
    have hclosed : T.IsClosedWalk x₀ lt := ⟨hwt, hh, hlast⟩
    have hcontr : T.WalkHomotopic lt [x₀] := hT x₀ lt hclosed
    have hdown : B.WalkHomotopic (lt.map p) ([x₀].map p) := hp.map_walkHomotopic hcontr
    rw [hmap] at hdown
    refine Pi1.mk_eq_mk.2 ?_
    simpa [WalkHtpy] using hdown
  refine Quotient.ind fun w => Quotient.ind fun w' => ?_
  intro hEq
  have hEq' : hp.liftEnd w x₀ = hp.liftEnd w' x₀ := hEq
  have hcancel : hp.liftEnd (w.append w'.reverse) x₀ = x₀ := by
    rw [hp.liftEnd_append, hEq']
    exact hp.liftEnd_reverse w' rfl
  have h1 : Pi1.mk (w.append w'.reverse) = (1 : B.Pi1 (p x₀)) := key _ hcancel
  have h2 : Pi1.mk w * (Pi1.mk w')⁻¹ = 1 := by
    rw [Pi1.inv_mk, Pi1.mul_mk]
    exact h1
  have := mul_inv_eq_one.mp h2
  exact this

/-- **Surjectivity of the monodromy** onto the fibre, for a connected covering complex. -/
theorem monodromy_surjective (hp : IsCovering T B p) (hTc : T.WalkConnected) (x₀ : Vt) :
    ∀ z : Vt, p z = p x₀ → ∃ g : B.Pi1 (p x₀), hp.monodromy x₀ g = z := by
  intro z hz
  obtain ⟨lt, hwt, hh, hlast⟩ := hTc x₀ z
  have hmapwalk : B.IsWalkFrom (p x₀) (p x₀) (lt.map p) := by
    refine ⟨hp.map_isWalk hwt, ?_, ?_⟩
    · rw [List.head?_map, hh]; rfl
    · rw [List.getLast?_map, hlast]
      simp [hz]
  obtain ⟨w, hwsupp⟩ := exists_walk_of_isWalkFrom hmapwalk
  refine ⟨Pi1.mk w, ?_⟩
  have := hp.liftEnd_eq_of_lift w hwt hh (by rw [hwsupp])
  rw [hlast] at this
  simpa using this.symm

/-- **The monodromy is a bijection onto the fibre** when the covering complex is connected and
simply connected: the combinatorial form of `π₁(B, b₀) ≅ p⁻¹(b₀)` for the universal cover. -/
theorem monodromy_bijective (hp : IsCovering T B p) (hTc : T.WalkConnected)
    (hT : T.SimplyConnectedW) (x₀ : Vt) :
    Function.Bijective (fun g : B.Pi1 (p x₀) => (⟨hp.monodromy x₀ g, hp.monodromy_mem_fibre x₀ g⟩ :
      {z : Vt // p z = p x₀})) := by
  constructor
  · intro g g' h
    exact hp.monodromy_injective hT x₀ (congrArg Subtype.val h)
  · rintro ⟨z, hz⟩
    obtain ⟨g, hg⟩ := hp.monodromy_surjective hTc x₀ z hz
    exact ⟨g, Subtype.ext hg⟩

/-! ### The map induced on fundamental groups -/

/-- The image of a walk of the covering complex. -/
def mapWalk (hp : IsCovering T B p) :
    ∀ {x y : Vt}, (toSimpleGraph T).Walk x y → (toSimpleGraph B).Walk (p x) (p y)
  | _, _, SimpleGraph.Walk.nil => SimpleGraph.Walk.nil
  | _, _, SimpleGraph.Walk.cons h q => SimpleGraph.Walk.cons (hp.map_adj h) (hp.mapWalk q)

@[simp] theorem mapWalk_nil (hp : IsCovering T B p) (x : Vt) :
    hp.mapWalk (SimpleGraph.Walk.nil (u := x)) = SimpleGraph.Walk.nil := rfl

@[simp] theorem mapWalk_cons (hp : IsCovering T B p) {x y z : Vt}
    (h : (toSimpleGraph T).Adj x y) (q : (toSimpleGraph T).Walk y z) :
    hp.mapWalk (SimpleGraph.Walk.cons h q)
      = SimpleGraph.Walk.cons (hp.map_adj h) (hp.mapWalk q) := rfl

theorem support_mapWalk (hp : IsCovering T B p) :
    ∀ {x y : Vt} (w : (toSimpleGraph T).Walk x y), (hp.mapWalk w).support = w.support.map p := by
  intro x y w
  induction w with
  | nil => simp
  | cons h q ih => simp [ih]

theorem mapWalk_append (hp : IsCovering T B p) :
    ∀ {x y z : Vt} (w : (toSimpleGraph T).Walk x y) (v : (toSimpleGraph T).Walk y z),
      hp.mapWalk (w.append v) = (hp.mapWalk w).append (hp.mapWalk v) := by
  intro x y z w v
  induction w with
  | nil => rfl
  | cons h q ih => simp [SimpleGraph.Walk.cons_append, ih]

/-- **The homomorphism induced by a covering on fundamental groups.** -/
def pi1Map (hp : IsCovering T B p) (x₀ : Vt) : T.Pi1 x₀ →* B.Pi1 (p x₀) where
  toFun := Quotient.lift (fun w => Pi1.mk (hp.mapWalk w))
    (by
      intro w w' h
      refine Pi1.mk_eq_mk.2 ?_
      show B.WalkHomotopic (hp.mapWalk w).support (hp.mapWalk w').support
      rw [support_mapWalk, support_mapWalk]
      exact hp.map_walkHomotopic h)
  map_one' := rfl
  map_mul' := by
    refine Quotient.ind fun w => Quotient.ind fun v => ?_
    show Pi1.mk (hp.mapWalk (w.append v)) = Pi1.mk (hp.mapWalk w) * Pi1.mk (hp.mapWalk v)
    rw [Pi1.mul_mk, hp.mapWalk_append]

@[simp] theorem pi1Map_mk (hp : IsCovering T B p) (x₀ : Vt)
    (w : (toSimpleGraph T).Walk x₀ x₀) : hp.pi1Map x₀ (Pi1.mk w) = Pi1.mk (hp.mapWalk w) := rfl

/-- **A covering is injective on fundamental groups.** -/
theorem pi1Map_injective (hp : IsCovering T B p) (x₀ : Vt) :
    Function.Injective (hp.pi1Map x₀) := by
  refine (injective_iff_map_eq_one _).2 ?_
  refine Quotient.ind fun w => ?_
  intro hw
  have h1 : B.WalkHomotopic (hp.mapWalk w).support
      (SimpleGraph.Walk.nil : (toSimpleGraph B).Walk (p x₀) (p x₀)).support :=
    Pi1.mk_eq_mk.1 hw
  rw [support_mapWalk] at h1
  have hdown : B.WalkHomotopic (w.support.map p) [p x₀] := by simpa using h1
  obtain ⟨lt', hw', hh', hmap', hhom⟩ := hp.lift_walkHomotopic hdown (isWalk_support w) rfl
  have hlt' : lt' = [x₀] := by
    cases lt' with
    | nil => simp at hmap'
    | cons z t =>
        have hz : p z = p x₀ ∧ t.map p = [] := by simpa using hmap'
        have ht : t = [] := List.map_eq_nil_iff.1 hz.2
        subst ht
        have hzx : z = x₀ := by
          have hhw : w.support.head? = some x₀ := (isWalkFrom_support' w).2.1
          rw [hhw] at hh'
          simpa using hh'
        rw [hzx]
  rw [hlt'] at hhom
  exact Pi1.mk_eq_mk.2 (by simpa [WalkHtpy] using hhom)

end IsCovering

end SquareComplex

end FiniteChains
