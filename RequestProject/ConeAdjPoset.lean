import RequestProject.OrderCxMonodromy

/-!
# Adjoining cone points over prescribed subsets of a poset

The poset model of a presentation complex is obtained from the mapping cylinder of the
attaching circles by coning off each circle.  This file provides that last step in general
form: given a preorder `P`, an index type `T` of new points and, for every `t : T`, a set
`S t ⊆ P` of elements it is to dominate, the preorder

    `ConeAdj P T S = P ⊕ T`

puts `t` above the *down-closure* of `S t` and adds no other relation.  Taking the down-closure
is what makes transitivity automatic; on a down-closed `S t` — the only case used — it changes
nothing.

Also provided:

* `FiniteChains.Comb.OrdCocycle.comap` — a cocycle pulls back along a monotone map;
* `FiniteChains.Comb.OrdCocycle.coneAdj` — a cocycle on `P` extends to `ConeAdj P T S` as soon
  as for every cone point `t` a *trivialisation* `h t : P → G` of the cocycle on the elements
  under `t` is given; this is the exact point at which a relator of the presentation has to die
  in the receiving group;
* `FiniteChains.Comb.htpy_nil_of_pathIn_le` — the cone lemma in the form used later: a loop all
  of whose edges lie under a fixed element is null-homotopic.
-/

namespace FiniteChains
namespace Comb

universe u v

/-! ### Pullback of a cocycle -/

section Comap

variable {P Q : Type u} [Preorder P] [Preorder Q] {G : Type v} [Group G]

/-- A cocycle pulls back along a monotone map. -/
def OrdCocycle.comap (f : P → Q) (hf : Monotone f) (c : OrdCocycle Q G) : OrdCocycle P G where
  val a b := c.val (f a) (f b)
  comp hab hbc := c.comp (hf hab) (hf hbc)

@[simp] theorem OrdCocycle.comap_val (f : P → Q) (hf : Monotone f) (c : OrdCocycle Q G)
    (a b : P) : (c.comap f hf).val a b = c.val (f a) (f b) := rfl

end Comap

/-! ### The poset with adjoined cone points -/

variable {P : Type u} [Preorder P] {T : Type u}

/-- The preorder `P` with a new point above the down-closure of `S t` for every `t : T`. -/
def ConeAdj (_S : T → P → Prop) : Type u := P ⊕ T

namespace ConeAdj

variable {S : T → P → Prop}

/-- The inclusion of the original poset. -/
def inc (p : P) : ConeAdj S := Sum.inl p

/-- The cone point attached to `t`. -/
def apex (t : T) : ConeAdj S := Sum.inr t

/-- The order of `ConeAdj`: the old order on `P`, a new point above everything below some
element of `S t`, and no relation between two distinct new points. -/
protected def le (S : T → P → Prop) : ConeAdj S → ConeAdj S → Prop
  | Sum.inl p, Sum.inl q => p ≤ q
  | Sum.inl p, Sum.inr t => ∃ r, S t r ∧ p ≤ r
  | Sum.inr _, Sum.inl _ => False
  | Sum.inr t, Sum.inr t' => t = t'

instance : Preorder (ConeAdj S) where
  le := ConeAdj.le S
  le_refl p := by
    cases p with
    | inl x => exact le_refl x
    | inr t => rfl
  le_trans p q r hpq hqr := by
    cases p with
    | inl x =>
        cases q with
        | inl y =>
            cases r with
            | inl z => exact le_trans hpq hqr
            | inr t =>
                obtain ⟨w, hw, hyw⟩ := hqr
                exact ⟨w, hw, le_trans hpq hyw⟩
        | inr t =>
            cases r with
            | inl z => exact hqr.elim
            | inr t' =>
                cases hqr
                exact hpq
    | inr t =>
        cases q with
        | inl y => exact hpq.elim
        | inr t' =>
            cases r with
            | inl z => exact hqr.elim
            | inr t'' => exact hpq.trans hqr

@[simp] theorem inc_le_inc {p q : P} : (inc p : ConeAdj S) ≤ inc q ↔ p ≤ q := Iff.rfl

@[simp] theorem inc_le_apex {p : P} {t : T} :
    (inc p : ConeAdj S) ≤ apex t ↔ ∃ r, S t r ∧ p ≤ r := Iff.rfl

@[simp] theorem not_apex_le_inc {p : P} {t : T} : ¬ (apex t : ConeAdj S) ≤ inc p := id

theorem inc_monotone : Monotone (inc : P → ConeAdj S) := fun _ _ h => h

/-- The defining relation: an element of `S t` lies under the cone point `t`. -/
theorem inc_le_apex_of_mem {p : P} {t : T} (h : S t p) : (inc p : ConeAdj S) ≤ apex t :=
  ⟨p, h, le_refl p⟩

omit [Preorder P] in
theorem inc_injective : Function.Injective (inc : P → ConeAdj S) := fun _ _ h => Sum.inl_injective h

end ConeAdj

/-! ### Extending a cocycle over the cone points -/

variable {G : Type v} [Group G] {S : T → P → Prop}

/-- The extension of a cocycle over the adjoined cone points, given a trivialisation `h t` of
the cocycle under each cone point. -/
def OrdCocycle.coneAdjVal (c : OrdCocycle P G) (h : T → P → G) :
    ConeAdj S → ConeAdj S → G
  | Sum.inl p, Sum.inl q => c.val p q
  | Sum.inl p, Sum.inr t => h t p
  | Sum.inr _, Sum.inl _ => 1
  | Sum.inr _, Sum.inr _ => 1

/-- **Extension of a cocycle over the cone points.**  The hypothesis is that `h t` trivialises
the cocycle on the elements lying under the cone point `t`. -/
def OrdCocycle.coneAdj (c : OrdCocycle P G) (h : T → P → G)
    (hh : ∀ (t : T) {p q : P}, p ≤ q → (ConeAdj.inc q : ConeAdj S) ≤ ConeAdj.apex t →
      c.val p q * h t q = h t p) :
    OrdCocycle (ConeAdj S) G where
  val := c.coneAdjVal h
  comp := by
    rintro (p | t) (q | t') (r | t'') hpq hqr
    · exact c.comp hpq hqr
    · exact hh t'' hpq hqr
    · exact absurd hqr (fun x => x)
    · cases (hqr : t' = t'')
      show h t' p * 1 = h t' p
      rw [mul_one]
    · exact absurd hpq (fun x => x)
    · exact absurd hpq (fun x => x)
    · exact absurd hqr (fun x => x)
    · show (1 : G) * 1 = 1
      rw [mul_one]

@[simp] theorem OrdCocycle.coneAdj_val_inc (c : OrdCocycle P G) (h : T → P → G) (hh) (p q : P) :
    (c.coneAdj (S := S) h hh).val (ConeAdj.inc p) (ConeAdj.inc q) = c.val p q := rfl

@[simp] theorem OrdCocycle.coneAdj_val_apex (c : OrdCocycle P G) (h : T → P → G) (hh)
    (p : P) (t : T) :
    (c.coneAdj (S := S) h hh).val (ConeAdj.inc p) (ConeAdj.apex t) = h t p := rfl

/-! ### The cone lemma in the form used below -/

/-- **A loop all of whose edges lie under a fixed element is null-homotopic.** -/
theorem htpy_nil_of_pathIn_le {Pp : Type u} [Preorder Pp] (d : Pp) {v : Pp} (hv : v ≤ d)
    {l : List ((orderCx Pp).E × Bool)}
    (hp : IsPath (orderCx Pp).src (orderCx Pp).tgt l v v)
    (hl : PathIn (fun x => x ≤ d) l) :
    Htpy (orderCx Pp) v v l [] :=
  htpy_nil_of_pathIn_le_top (A := fun x => x ≤ d) (le_refl d) (fun _ hx => hx) hv hp hl

end Comb
end FiniteChains
