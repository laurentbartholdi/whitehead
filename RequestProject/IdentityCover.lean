module

public import RequestProject.CombData

@[expose] public section

/-!
# Remark 2: an acyclic two-complex satisfies condition (2) through its identity cover

Condition (2) of Theorem A asks for a connected acyclic regular cover.  The paper notes that
an acyclic two-complex satisfies it trivially, the cover being the identity map.  This file
verifies that remark in the combinatorial model: the identity cellular map is a covering, it
is regular with trivial deck group, and therefore

`FiniteChains.Comb.hasAcyclicRegularCover_of_isAcyclic` — a connected acyclic two-complex has
a connected acyclic regular cover.

* `FiniteChains.Comb.isCovering_id` — the identity map is a combinatorial covering;
* `FiniteChains.Comb.trivialDeckAction` — the trivial action of the trivial group;
* `FiniteChains.Comb.isRegular_id` — the identity covering is regular with trivial deck group.
-/

namespace FiniteChains
namespace Comb

universe u

variable {X : Complex2.{u}}

/-- The identity cellular map is a covering. -/
theorem isCovering_id (X : Complex2.{u}) : IsCovering (Hom.id X) where
  surjV := fun a => ⟨a, rfl⟩
  germ := by
    intro a
    constructor
    · intro eb eb' h
      exact Subtype.ext (congrArg Subtype.val h)
    · intro eb
      exact ⟨⟨eb.1, eb.2⟩, Subtype.ext rfl⟩
  cell := by
    constructor
    · intro f f' h
      exact congrArg (fun z => z.1.1) h
    · rintro ⟨⟨g, v⟩, hv⟩
      exact ⟨g, Subtype.ext (Prod.ext rfl hv)⟩

/-- The trivial action of the trivial group on a complex. -/
def trivialDeckAction (X : Complex2.{u}) : DeckAction X PUnit.{u + 1} where
  smulV _ a := a
  smulE _ e := e
  smulF _ f := f
  one_smulV _ := rfl
  mul_smulV _ _ _ := rfl
  one_smulE _ := rfl
  mul_smulE _ _ _ := rfl
  one_smulF _ := rfl
  mul_smulF _ _ _ := rfl
  src_smul _ _ := rfl
  tgt_smul _ _ := rfl
  base_smul _ _ := rfl
  att_smul _ f := by simp

/-- The identity covering is regular, with trivial deck group. -/
theorem isRegular_id (X : Complex2.{u}) :
    IsRegular (Hom.id X) (trivialDeckAction X) where
  compat _ _ := rfl
  simply_transitive := by
    intro a b hab
    exact ⟨PUnit.unit, hab, fun _ _ => Subsingleton.elim _ _⟩

/-- **Remark 2 of the paper.**  A connected acyclic two-complex satisfies condition (2) of
Theorem A through its identity cover. -/
theorem hasAcyclicRegularCover_of_isAcyclic (hconn : IsConnected X) (hacyc : IsAcyclic X) :
    HasAcyclicRegularCover X :=
  ⟨X, PUnit.{u + 1}, inferInstance, Hom.id X, trivialDeckAction X,
    isCovering_id X, isRegular_id X, hconn, hacyc⟩

/-- The same statement in the interface of Theorem A. -/
theorem hasAcyclicRegularCover_combData_of_isAcyclic (hconn : IsConnected X)
    (hacyc : IsAcyclic X) : FiniteChains.HasAcyclicRegularCover combData X :=
  (hasAcyclicRegularCover_combData_iff X).2 (hasAcyclicRegularCover_of_isAcyclic hconn hacyc)

end Comb
end FiniteChains
