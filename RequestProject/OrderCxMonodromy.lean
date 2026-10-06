module

public import RequestProject.OrderComplexGluing

@[expose] public section

/-!
# Reading homomorphisms out of the fundamental group of an order complex

This file supplies the two elementary tools used to compare the order complex of a poset with a
group presentation without computing its fundamental group.

* `FiniteChains.Comb.OrdCocycle P G` — a *cocycle* on the preorder `P` with values in the group
  `G`: an element `c.val h ∈ G` for every comparability `h : a ≤ b`, multiplicative along chains
  (`c.val hab * c.val hbc = c.val (hab.trans hbc)`).  Equivalently a functor from `P`, viewed as
  a category, to `G` viewed as a one-object category.
* `FiniteChains.Comb.OrdCocycle.monodromy` — the induced **reading homomorphism**
  `π₁(orderCx P, x) →* G`: an edge of the order complex is read off by the cocycle, the relation
  of a two-cell `a ≤ b ≤ c` is exactly the cocycle identity, and a backtrack cancels.  No
  spanning tree and no computation of `π₁` is involved.
* `FiniteChains.Comb.htpy_nil_of_pathIn_le_top` — the **cone lemma**: a loop of the ambient
  order complex all of whose edges lie in a subposet possessing a largest element is
  null-homotopic in the ambient complex.

Both are used to build the comparison of a presentation with the order complex of the poset
model of its presentation complex.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Comb

universe u v

variable {P : Type u} [Preorder P] {G : Type v} [Group G]

/-! ### Cocycles on a preorder -/

/-- A cocycle on a preorder with values in a group: a value for every ordered pair, required to
be multiplicative along chains.  On comparable pairs this is the same thing as a functor from
`P`, viewed as a category, to `G`; the values on incomparable pairs are irrelevant. -/
structure OrdCocycle (P : Type u) [Preorder P] (G : Type v) [Group G] where
  /-- The value on a pair of elements. -/
  val : P → P → G
  /-- Multiplicativity along a chain. -/
  comp : ∀ {a b c : P}, a ≤ b → b ≤ c → val a b * val b c = val a c

namespace OrdCocycle

variable (c : OrdCocycle P G)

@[simp] theorem val_refl (a : P) : c.val a a = 1 := by
  have h := c.comp (le_refl a) (le_refl a)
  simpa using h

/-- The value of the cocycle on an oriented edge of the order complex. -/
def readGerm (g : (orderCx P).E × Bool) : G :=
  if g.2 then c.val g.1.1.1 g.1.1.2 else (c.val g.1.1.1 g.1.1.2)⁻¹

@[simp] theorem readGerm_ordPos {a b : P} (h : a ≤ b) : c.readGerm (ordPos h) = c.val a b := rfl

@[simp] theorem readGerm_ordNeg {a b : P} (h : a ≤ b) :
    c.readGerm (ordNeg h) = (c.val a b)⁻¹ := rfl

@[simp] theorem readGerm_revGerm (g : (orderCx P).E × Bool) :
    c.readGerm (revGerm (X := orderCx P) g) = (c.readGerm g)⁻¹ := by
  obtain ⟨e, b⟩ := g
  cases b <;> simp [readGerm, revGerm]

/-- The value of the cocycle on an edge path: the product of the values of its edges. -/
def readPath (l : List ((orderCx P).E × Bool)) : G := (l.map c.readGerm).prod

@[simp] theorem readPath_nil : c.readPath [] = 1 := rfl

@[simp] theorem readPath_cons (g : (orderCx P).E × Bool) (l : List ((orderCx P).E × Bool)) :
    c.readPath (g :: l) = c.readGerm g * c.readPath l := by
  simp [readPath]

@[simp] theorem readPath_append (l l' : List ((orderCx P).E × Bool)) :
    c.readPath (l ++ l') = c.readPath l * c.readPath l' := by
  simp [readPath]

@[simp] theorem readPath_att (t : OrdTri P) : c.readPath ((orderCx P).att t) = 1 := by
  obtain ⟨⟨a, b, d⟩, hab, hbd⟩ := t
  show c.readGerm (ordPos hab) * (c.readGerm (ordPos hbd) *
    (c.readGerm (ordNeg (hab.trans hbd)) * 1)) = 1
  rw [readGerm_ordPos, readGerm_ordPos, readGerm_ordNeg, mul_one, ← mul_assoc, c.comp hab hbd,
    mul_inv_cancel]

/-- An elementary cancellation does not change the value of a path. -/
theorem readPath_cancels {l l' : List ((orderCx P).E × Bool)}
    (h : Cancels (orderCx P) l l') : c.readPath l = c.readPath l' := by
  rcases h with ⟨p, q, g, hl, hl'⟩ | ⟨p, q, t, hl, hl'⟩
  · subst hl; subst hl'
    simp only [c.readPath_append, c.readPath_cons, c.readGerm_revGerm, mul_inv_cancel_left]
  · subst hl; subst hl'
    simp only [c.readPath_append, c.readPath_att, one_mul, mul_one]

/-- Homotopic paths have the same value. -/
theorem readPath_htpy {a b : P} {l l' : List ((orderCx P).E × Bool)}
    (h : Htpy (orderCx P) a b l l') : c.readPath l = c.readPath l' := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      rcases hstep with hs | hs
      · exact ih.trans (c.readPath_cancels hs.2.2)
      · exact ih.trans (c.readPath_cancels hs.2.2).symm

/-- **The reading homomorphism** attached to a cocycle: the monodromy of the associated flat
bundle, read on edge loops. -/
def monodromy (x : P) : Pi1 (orderCx P) x →* G where
  toFun := Quotient.lift (fun p : Loop (orderCx P) x => c.readPath p.1)
    (fun _ _ h => c.readPath_htpy h)
  map_one' := rfl
  map_mul' := by
    rintro ⟨p⟩ ⟨q⟩
    exact c.readPath_append p.1 q.1

@[simp] theorem monodromy_mk (x : P) (p : Loop (orderCx P) x) :
    c.monodromy x (Pi1.mk p) = c.readPath p.1 := rfl

end OrdCocycle

/-! ### The cone lemma -/

/-- **A loop inside a subposet with a largest element is null-homotopic.**  The subposet need
not be an interval: all that is used is an element of `A` above every element of `A`. -/
theorem htpy_nil_of_pathIn_le_top {A : P → Prop} {d : P} (hd : A d)
    (hAd : ∀ x, A x → x ≤ d) {v : P} (hv : A v) {l : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt l v v) (hl : PathIn A l) :
    Htpy (orderCx P) v v l [] := by
  refine htpy_nil_of_pathIn ?_ hv hp hl
  refine simplyConnected_orderCx (P := {p : P // A p}) ⟨d, hd⟩ id (fun x => le_refl x)
    (fun x => hAd x.1 x.2) ?_
  intro x y h
  exact h

end Comb
end FiniteChains
