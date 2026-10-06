import RequestProject.SubstOneWayQuotient
import RequestProject.PresPosetAlphaW

/-!
# The one-way comparison over a model built on prescribed relator words

This is `RequestProject/SubstOneWayQuotient.lean` with the base of the chamber construction taken
to be the poset model `PresPos w` of the presentation complex of `ρ` built on a **prescribed**
family `w` of relator words, `FreeGroup.mk (w j) = ρ j`.  Nothing changes in the argument: the
marked comparison of `ρ` with the fundamental group of the model is injective
(`FiniteChains.PresModel.alphaHomW_injective`) and the inclusion of the base copy in the
quotient `Q = Z/Γ` is injective on fundamental groups
(`FiniteChains.Davis.pi1Map_qNew_injective`).
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

/-- **The comparison of the source presentation with the quotient**, over the model built on the
prescribed relator words. -/
noncomputable def baseToQuotientW {α J : Type u} (ρ : J → FreeGroup α)
    (w : J → List (α × Bool)) (hw : ∀ j, FreeGroup.mk (w j) = ρ j)
    (att : NeSpx A →o PresPos w) :
    PresGroup ρ →*
      Comb.Pi1 (orderCx (Qpos A (PresPos w) att)) (qNew (A := A) (att := att) (ptBase w)) :=
  (Comb.pi1Map (orderCxMap (qNew (A := A) (X := PresPos w) (att := att)) qNew_monotone)
      (ptBase w)).comp (alphaHomW ρ w hw)

/-- **The comparison is injective.** -/
theorem baseToQuotientW_injective {α J : Type u} (ρ : J → FreeGroup α)
    (w : J → List (α × Bool)) (hw : ∀ j, FreeGroup.mk (w j) = ρ j)
    (att : NeSpx A →o PresPos w) :
    Function.Injective (baseToQuotientW (A := A) ρ w hw att) := by
  intro x y h
  exact alphaHomW_injective ρ w hw
    (pi1Map_qNew_injective (A := A) (att := att) (ptBase w) h)

/-- **The one-way comparison for the article's marked blocks**, over the model built on the
prescribed relator words. -/
theorem injective_substHomF_of_markedBlocksW {α Jr Sx : Type u} {Zt Mt Su : Sx → Type u}
    (ρ : Jr ⊕ Sx → FreeGroup α) (w : Jr ⊕ Sx → List (α × Bool))
    (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (att : NeSpx A →o PresPos w)
    (u : ∀ s : Sx, Su s → FreeGroup α)
    (beta : ∀ s : Sx, Mt s → FreeGroup (Su s ⊕ Zt s))
    (hfill : BlockFamily.FilledF ρ (fun s m => BlockFamily.blockSubst u s (beta s m)))
    (bq : ∀ s : Sx, FreeGroup (Su s ⊕ Zt s) →*
      Comb.Pi1 (orderCx (Qpos A (PresPos w) att)) (qNew (A := A) (att := att) (ptBase w)))
    (hmark : ∀ (s : Sx) (x : Su s),
      bq s (FreeGroup.of (Sum.inl x))
        = baseToQuotientW (A := A) ρ w hw att (QuotientGroup.mk (u s x)))
    (hrel : ∀ (s : Sx) (m : Mt s), bq s (beta s m) = 1) :
    Function.Injective
      (BlockFamily.substHomF ρ (fun s m => BlockFamily.blockSubst u s (beta s m)) hfill) :=
  BlockFamily.injective_substHomF_of_markedBlock u beta hfill (baseToQuotientW (A := A) ρ w hw att)
    (baseToQuotientW_injective (A := A) ρ w hw att) bq hmark hrel

end Davis
end FiniteChains
