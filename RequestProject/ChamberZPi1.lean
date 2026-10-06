module

public import RequestProject.ChamberZPoset
public import RequestProject.OrderComplexGluing

@[expose] public section

/-!
# When a copy of the base splits off the fundamental group of `Z`

The attaching map `att` of `RequestProject/ChamberZPoset.lean` is defined on the **nonempty**
simplices only: no extension over the cone point of a chamber is assumed, because the cone point
of a modified chamber is exactly what is removed.

If, in addition, the attaching map does extend monotonically over the cone — that is, if there
is a monotone `attExt : Finset V →o X` agreeing with `att` on nonempty simplices — then the
whole of `Z` retracts monotonically onto the base poset, and every copy of the base is a
**split** subgroup of `π₁(Z)`:

* `FiniteChains.Davis.zRetrAll` — the retraction `Z → X` under that hypothesis;
* `FiniteChains.Davis.pi1Map_zNew_injective` — `π₁(X) → π₁(Z)` is then injective for every copy
  of the base.

The hypothesis is a genuine restriction: it says that the attaching map of the block dies in the
base.  Without it the injectivity of a copy of the base is **not** proved here; it is the
free-product argument along the simply connected attaching intersections `J_w`, and it remains
open (see `THEOREM-A-OBLIGATIONS.md`).
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Davis

open RACG Mirror Comb

universe u

variable {V : Type u} [DecidableEq V] {A : CommRel V} {X : Type u} [Preorder X]
  {M : CayGroup A → Prop} {att : NeSpx A →o X}
  (attExt : Finset V →o X)
  (hext : ∀ (σ : Finset V) (h : σ.Nonempty ∧ IsSimplex A σ), attExt σ = att ⟨σ, h⟩)

/-- **The retraction of `Z` onto the base poset**, available when the attaching map extends
monotonically over the cone point: an old cell of type `σ` goes to `attExt σ`, a cell of an
adjoined copy of `X` goes to itself. -/
def zRetrAll : Zpos A X M att → X
  | Sum.inl p => attExt p.1.spx
  | Sum.inr vx => vx.2

@[simp] theorem zRetrAll_zNew (w : {w : CayGroup A // M w}) (x : X) :
    zRetrAll (att := att) attExt (zNew w x) = x := rfl

include hext in
theorem zRetrAll_monotone :
    Monotone (zRetrAll (A := A) (X := X) (M := M) (att := att) attExt) := by
  rintro (p | ⟨u, x⟩) (q | ⟨v, y⟩) h
  · exact attExt.monotone (show p.1.spx ≤ q.1.spx from h.1)
  · exact h.elim
  · obtain ⟨hne, hx⟩ := h.2
    rw [zRetrAll, zRetrAll, hext q.1.spx ⟨hne, q.1.isSimplex⟩]
    exact hx
  · exact h.2

/-- The inclusion of a copy of the base is monotone. -/
theorem zNew_monotone (w : {w : CayGroup A // M w}) :
    Monotone (zNew (A := A) (X := X) (M := M) (att := att) w) :=
  fun _ _ h => ⟨rfl, h⟩

include hext in
/-- **A copy of the base splits off `π₁(Z)` when the attaching map extends over the cone.**  The
inclusion of a copy of `X` is then split by the retraction `zRetrAll`, so the induced map of
fundamental groups is injective. -/
theorem pi1Map_zNew_injective (w : {w : CayGroup A // M w}) (x : X) :
    Function.Injective
      (Comb.pi1Map (orderCxMap (zNew (A := A) (X := X) (M := M) (att := att) w)
        (zNew_monotone w)) x) := by
  have hleft : Function.LeftInverse
      (Comb.pi1Map (orderCxMap (zRetrAll (A := A) (X := X) (M := M) (att := att) attExt)
        (zRetrAll_monotone attExt hext))
        (zNew (A := A) (X := X) (M := M) (att := att) w x))
      (Comb.pi1Map (orderCxMap (zNew (A := A) (X := X) (M := M) (att := att) w)
        (zNew_monotone w)) x) := by
    have hlist : ∀ q : List ((orderCx X).E × Bool),
        Comb.mapPath (orderCxMap (zRetrAll (A := A) (X := X) (M := M) (att := att) attExt)
            (zRetrAll_monotone attExt hext))
          (Comb.mapPath (orderCxMap (zNew (A := A) (X := X) (M := M) (att := att) w)
            (zNew_monotone w)) q) = q := by
      intro q
      induction q with
      | nil => rfl
      | cons a t ih =>
          simp only [Comb.mapPath, List.map_cons] at ih ⊢
          rw [ih]
          exact congrArg (fun e => e :: t) (Prod.ext (Subtype.ext rfl) rfl)
    intro g
    induction g using Quotient.inductionOn with
    | h p =>
        exact congrArg (fun l : Comb.Loop (orderCx X) x => Quotient.mk _ l)
          (Subtype.ext (hlist p.1))
  exact hleft.injective

end Davis
end FiniteChains
