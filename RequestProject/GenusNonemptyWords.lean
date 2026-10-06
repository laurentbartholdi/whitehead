import RequestProject.GenusApply
import RequestProject.PresPosetConnected
import RequestProject.PresPosetPartialOrder

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel
variable {α Jr : Type} (ρ : Jr ⊕ PUnit → FreeGroup α)
  (a b : ℕ → α) (q : ℕ) [NeZero q]

/-- Nonempty representatives retaining the prescribed genus surface word. -/
noncomputable def genusNonemptyW : Jr ⊕ PUnit → List (α × Bool) :=
  Sum.elim (fun j => presNonemptyWords ρ (a 0) (Sum.inl j)) (fun _ => surfWord a b q)

theorem genusNonemptyW_ne_nil (j : Jr ⊕ PUnit) : genusNonemptyW ρ a b q j ≠ [] := by
  cases j with
  | inl j => exact presNonemptyWords_ne_nil ρ (a 0) (Sum.inl j)
  | inr s =>
    intro h
    have hl := congrArg List.length h
    change (surfWord a b q).length = 0 at hl
    rw (config := { transparency := .default }) [surfWord_length] at hl
    have := Nat.pos_of_neZero q
    omega

omit [NeZero q] in
theorem mk_genusNonemptyW
    (hr : ρ (Sum.inr PUnit.unit) = FreeGroup.mk (surfWord a b q)) :
    ∀ j, FreeGroup.mk (genusNonemptyW ρ a b q j) = ρ j := by
  rintro (j | s)
  · exact mk_presNonemptyWords ρ (a 0) (Sum.inl j)
  · cases s
    exact hr.symm

theorem genusNonemptyW_isConnected :
    IsConnected (orderCx (PresPos (genusNonemptyW ρ a b q))) :=
  presPos_isConnected _ (genusNonemptyW_ne_nil ρ a b q)

noncomputable abbrev genusNonemptyAtt :
    NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))) →o PresPos (genusNonemptyW ρ a b q) :=
  surfAtt (w := genusNonemptyW ρ a b q) (j₀ := Sum.inr PUnit.unit)
    (genus_hM a b q) (genus_hvlab a b q) (genus_helb a b q) (gc q)

theorem genusNonemptyAtt_base :
    genusNonemptyAtt ρ a b q (gBase q) = ptBase (genusNonemptyW ρ a b q) := by
  rw (config := { transparency := .default }) [gBase, att_V, vertLab_of_even (by rw (config := { transparency := .default }) [cyc_mod_two])]
  rfl

end FiniteChains.Davis.Genus
