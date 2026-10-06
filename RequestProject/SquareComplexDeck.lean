module

public import RequestProject.SquareComplexMonodromy
public import RequestProject.SquareComplexUniversalCover

@[expose] public section

/-!
# Deck transformations of a universal covering

For a covering `p : T → B` of square complexes with `T` connected and simply connected, the deck
transformations — the permutations of `T` which commute with `p` and preserve edges — form a
group acting simply transitively on each fibre, and that group is the fundamental group of the
base:

* `FiniteChains.SquareComplex.IsCovering.Deck` — the group of deck transformations;
* `FiniteChains.SquareComplex.IsCovering.deck_sq` — a deck transformation automatically
  preserves the two-cells;
* `FiniteChains.SquareComplex.IsCovering.deck_ext` — a deck transformation is determined by the
  image of one point;
* `FiniteChains.SquareComplex.IsCovering.exists_deck` — two points of a fibre are exchanged by a
  deck transformation;
* `FiniteChains.SquareComplex.IsCovering.deckMulEquiv` — **the deck group is the fundamental
  group of the base**.
-/

namespace FiniteChains

namespace SquareComplex

universe u v

variable {Vt : Type u} {Vb : Type v} {T : SquareComplex Vt} {B : SquareComplex Vb} {p : Vt → Vb}

namespace IsCovering

/-- The group of **deck transformations** of the covering `p`: the permutations of the covering
complex which commute with `p` and preserve edges. -/
def Deck (hp : IsCovering T B p) : Subgroup (Equiv.Perm Vt) where
  carrier := {e | (∀ x, p (e x) = p x) ∧ ∀ x y, T.adj x y → T.adj (e x) (e y)}
  mul_mem' := by
    rintro e f ⟨hep, hea⟩ ⟨hfp, hfa⟩
    refine ⟨fun x => ?_, fun x y hxy => hea _ _ (hfa _ _ hxy)⟩
    show p (e (f x)) = p x
    rw [hep, hfp]
  one_mem' := ⟨fun _ => rfl, fun _ _ h => h⟩
  inv_mem' := by
    rintro e ⟨hep, hea⟩
    have hinvp : ∀ x, p (e.symm x) = p x := by
      intro x
      have h := hep (e.symm x)
      rw [e.apply_symm_apply] at h
      exact h.symm
    refine ⟨hinvp, ?_⟩
    intro x y hxy
    have hb : B.adj (p (e.symm x)) (p (e.symm y)) := by
      rw [hinvp, hinvp]
      exact hp.map_adj hxy
    obtain ⟨w, ⟨hw1, hw2⟩, -⟩ := hp.lift_adj (e.symm x) hb
    have hew : T.adj x (e w) := by
      have h := hea _ _ hw1
      rwa [e.apply_symm_apply] at h
    have hpew : p (e w) = p y := by
      rw [hep w, hw2, hinvp]
    have hwy : e w = y := hp.edge_unique hew hxy hpew
    have hw : w = e.symm y := by
      rw [← hwy, e.symm_apply_apply]
    show T.adj (e.symm x) (e.symm y)
    rw [← hw]
    exact hw1

@[simp] theorem mem_Deck {hp : IsCovering T B p} {e : Equiv.Perm Vt} :
    e ∈ hp.Deck ↔ (∀ x, p (e x) = p x) ∧ ∀ x y, T.adj x y → T.adj (e x) (e y) := Iff.rfl

theorem deck_proj {hp : IsCovering T B p} {e : Equiv.Perm Vt} (he : e ∈ hp.Deck) (x : Vt) :
    p (e x) = p x := he.1 x

theorem deck_adj {hp : IsCovering T B p} {e : Equiv.Perm Vt} (he : e ∈ hp.Deck) {x y : Vt}
    (h : T.adj x y) : T.adj (e x) (e y) := he.2 x y h

/-- A deck transformation preserves the two-cells. -/
theorem deck_sq (hp : IsCovering T B p) {e : Equiv.Perm Vt} (he : e ∈ hp.Deck) {a b c d : Vt}
    (h : T.sq a b c d) : T.sq (e a) (e b) (e c) (e d) := by
  obtain ⟨hab, hbc, hcd, hda⟩ := T.sq_adj h
  have hbase : B.sq (p (e a)) (p b) (p c) (p d) := by
    rw [deck_proj he a]
    exact hp.map_sq h
  obtain ⟨b', c', d', hsq', hb', hc', hd'⟩ := hp.lift_sq (e a) hbase
  obtain ⟨hab', hbc', hcd', hda'⟩ := T.sq_adj hsq'
  have hb : b' = e b :=
    hp.edge_unique hab' (deck_adj he hab) (by rw [hb', deck_proj he b])
  subst hb
  have hc : c' = e c :=
    hp.edge_unique hbc' (deck_adj he hbc) (by rw [hc', deck_proj he c])
  subst hc
  have hd : d' = e d :=
    hp.edge_unique (T.adj_symm hda') (deck_adj he (T.adj_symm hda))
      (by rw [hd', deck_proj he d])
  subst hd
  exact hsq'

/-- A deck transformation commutes with lifting walks. -/
theorem deck_liftEnd (hp : IsCovering T B p) {e : Equiv.Perm Vt} (he : e ∈ hp.Deck) :
    ∀ {b c : Vb} (w : (toSimpleGraph B).Walk b c) (x : Vt), p x = b →
      hp.liftEnd w (e x) = e (hp.liftEnd w x) := by
  intro b c w
  induction w with
  | nil => intro x _; rfl
  | @cons b' m c' hadj q ih =>
      intro x hx
      have hadj₀ : B.adj (p x) m := by rw [hx]; exact hadj
      have hadj₁ : B.adj (p (e x)) m := by rw [deck_proj he x]; exact hadj₀
      obtain ⟨h1, h2⟩ := hp.edgeLift_spec hadj₀
      obtain ⟨h1', h2'⟩ := hp.edgeLift_spec hadj₁
      have hstep : hp.edgeLift (e x) m = e (hp.edgeLift x m) :=
        hp.edge_unique h1' (deck_adj he h1) (by rw [h2', deck_proj he (hp.edgeLift x m), h2])
      rw [liftEnd_cons, liftEnd_cons, hstep]
      exact ih _ h2

/-- The image of a walk under a deck transformation is a walk. -/
theorem deck_isWalk {hp : IsCovering T B p} {e : Equiv.Perm Vt} (he : e ∈ hp.Deck) :
    ∀ {lt : List Vt}, T.IsWalk lt → T.IsWalk (lt.map e) := by
  intro lt
  induction lt with
  | nil => intro _; simp [IsWalk]
  | cons a t ih =>
      cases t with
      | nil => intro _; simp [IsWalk]
      | cons b s =>
          intro hlt
          rw [IsWalk, List.isChain_cons_cons] at hlt
          simp only [List.map_cons]
          rw [IsWalk, List.isChain_cons_cons]
          exact ⟨deck_adj he hlt.1, ih hlt.2⟩

/-- **A deck transformation is determined by the image of one point.** -/
theorem deck_ext (hp : IsCovering T B p) (hTC : T.WalkConnected) {e f : Equiv.Perm Vt}
    (he : e ∈ hp.Deck) (hf : f ∈ hp.Deck) (x₀ : Vt) (h : e x₀ = f x₀) : e = f := by
  refine Equiv.ext fun y => ?_
  obtain ⟨lt, hlt, hh, hlast⟩ := hTC x₀ y
  have hhead : (lt.map e).head? = (lt.map f).head? := by
    simp [List.head?_map, hh, h]
  have himg : (lt.map e).map p = (lt.map f).map p := by
    simp only [List.map_map]
    refine List.map_congr_left ?_
    intro z _
    show p (e z) = p (f z)
    rw [deck_proj he z, deck_proj hf z]
  have heq := hp.lift_unique (deck_isWalk he hlt) (deck_isWalk hf hlt) hhead himg
  have hlaste : (lt.map e).getLast? = some (e y) := by rw [List.getLast?_map, hlast]; rfl
  have hlastf : (lt.map f).getLast? = some (f y) := by rw [List.getLast?_map, hlast]; rfl
  rw [heq, hlastf] at hlaste
  simpa using hlaste.symm

/-- **Two points of a fibre are exchanged by a deck transformation.** -/
theorem exists_deck (hp : IsCovering T B p) (hTC : T.WalkConnected) (hTSC : T.SimplyConnectedW)
    {x y : Vt} (h : p x = p y) : ∃ e : Equiv.Perm Vt, e ∈ hp.Deck ∧ e x = y := by
  obtain ⟨f, hbij, hfx, hfp, hadj, -⟩ :=
    exists_iso_of_universal hp hp hTC hTSC hTC hTSC (u₀ := x) (t₀ := y) h
  exact ⟨Equiv.ofBijective f hbij, ⟨fun z => hfp z, fun z w hzw => (hadj z w).1 hzw⟩, hfx⟩

/-! ### The deck group is the fundamental group of the base -/

/-- The deck transformation attached to a class of closed walks of the base: the one sending the
base point to the end point of the lift. -/
noncomputable def deckOf (hp : IsCovering T B p) (hTC : T.WalkConnected)
    (hTSC : T.SimplyConnectedW) (x₀ : Vt) (g : B.Pi1 (p x₀)) : Equiv.Perm Vt :=
  (hp.exists_deck hTC hTSC (x := x₀) (y := hp.monodromy x₀ g)
    (hp.monodromy_mem_fibre x₀ g).symm).choose

theorem deckOf_mem (hp : IsCovering T B p) (hTC : T.WalkConnected) (hTSC : T.SimplyConnectedW)
    (x₀ : Vt) (g : B.Pi1 (p x₀)) : hp.deckOf hTC hTSC x₀ g ∈ hp.Deck :=
  (hp.exists_deck hTC hTSC (x := x₀) (y := hp.monodromy x₀ g)
    (hp.monodromy_mem_fibre x₀ g).symm).choose_spec.1

theorem deckOf_base (hp : IsCovering T B p) (hTC : T.WalkConnected) (hTSC : T.SimplyConnectedW)
    (x₀ : Vt) (g : B.Pi1 (p x₀)) : hp.deckOf hTC hTSC x₀ g x₀ = hp.monodromy x₀ g :=
  (hp.exists_deck hTC hTSC (x := x₀) (y := hp.monodromy x₀ g)
    (hp.monodromy_mem_fibre x₀ g).symm).choose_spec.2

/-- The monodromy, as a homomorphism from the fundamental group of the base to the deck group. -/
noncomputable def deckHom (hp : IsCovering T B p) (hTC : T.WalkConnected)
    (hTSC : T.SimplyConnectedW) (x₀ : Vt) : B.Pi1 (p x₀) →* hp.Deck where
  toFun g := ⟨hp.deckOf hTC hTSC x₀ g, hp.deckOf_mem hTC hTSC x₀ g⟩
  map_one' := by
    refine Subtype.ext (hp.deck_ext hTC (hp.deckOf_mem hTC hTSC x₀ 1) hp.Deck.one_mem x₀ ?_)
    rw [hp.deckOf_base hTC hTSC x₀ 1]
    rfl
  map_mul' := by
    intro g h
    refine Subtype.ext (hp.deck_ext hTC (hp.deckOf_mem hTC hTSC x₀ (g * h))
      (hp.Deck.mul_mem (hp.deckOf_mem hTC hTSC x₀ g) (hp.deckOf_mem hTC hTSC x₀ h)) x₀ ?_)
    have hmul : hp.monodromy x₀ (g * h)
        = hp.deckOf hTC hTSC x₀ g (hp.monodromy x₀ h) := by
      refine Quotient.inductionOn₂ g h ?_
      intro w v
      show hp.liftEnd (w.append v) x₀ = hp.deckOf hTC hTSC x₀ (Pi1.mk w) (hp.liftEnd v x₀)
      rw [hp.liftEnd_append,
        ← hp.deck_liftEnd (hp.deckOf_mem hTC hTSC x₀ (Pi1.mk w)) v x₀ rfl,
        hp.deckOf_base hTC hTSC x₀ (Pi1.mk w)]
      rfl
    show hp.deckOf hTC hTSC x₀ (g * h) x₀
      = hp.deckOf hTC hTSC x₀ g (hp.deckOf hTC hTSC x₀ h x₀)
    rw [hp.deckOf_base hTC hTSC x₀ (g * h), hp.deckOf_base hTC hTSC x₀ h, hmul]

/-- **The deck group of a connected, simply connected covering is the fundamental group of the
base.** -/
noncomputable def deckMulEquiv (hp : IsCovering T B p) (hTC : T.WalkConnected)
    (hTSC : T.SimplyConnectedW) (x₀ : Vt) : B.Pi1 (p x₀) ≃* hp.Deck := by
  refine MulEquiv.ofBijective (hp.deckHom hTC hTSC x₀) ⟨?_, ?_⟩
  · intro g g' hgg
    have h1 : hp.deckOf hTC hTSC x₀ g x₀ = hp.deckOf hTC hTSC x₀ g' x₀ :=
      congrArg (fun z : hp.Deck => (z : Equiv.Perm Vt) x₀) hgg
    rw [hp.deckOf_base hTC hTSC x₀ g, hp.deckOf_base hTC hTSC x₀ g'] at h1
    exact hp.monodromy_injective hTSC x₀ h1
  · rintro ⟨e, he⟩
    obtain ⟨g, hg⟩ := hp.monodromy_surjective hTC x₀ (e x₀) (deck_proj he x₀)
    refine ⟨g, Subtype.ext (hp.deck_ext hTC (hp.deckOf_mem hTC hTSC x₀ g) he x₀ ?_)⟩
    show hp.deckOf hTC hTSC x₀ g x₀ = e x₀
    rw [hp.deckOf_base hTC hTSC x₀ g, hg]

end IsCovering

end SquareComplex

end FiniteChains
