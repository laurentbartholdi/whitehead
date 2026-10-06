module

public import RequestProject.ChamberQuotientAttachingCover

@[expose] public section

/-! The whole base star retracts down onto the actual inserted base. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

abbrev QBaseStar := {p : Qpos A X att // InQBaseStar p}

def qBaseStarToBase : QBaseStar (att := att) → X
  | ⟨.inl c, hp⟩ => att (qPositiveOldSimplex ⟨.inl c, trivial, hp⟩)
  | ⟨.inr x, _⟩ => x

theorem qBaseStarToBase_monotone : Monotone (qBaseStarToBase (att := att)) := by
  rintro ⟨p, hp⟩ ⟨r, hr⟩ h
  cases p with
  | inl c =>
    cases r with
    | inl d => exact att.monotone h.1
    | inr y => exact False.elim h
  | inr x =>
    cases r with
    | inl d =>
      obtain ⟨_, hn, hh⟩ := h
      exact hh
    | inr y => exact h

def qBaseStarRetraction (p : QBaseStar (att := att)) : Qpos A X att :=
  qNew (qBaseStarToBase p)

theorem qBaseStarRetraction_monotone : Monotone (qBaseStarRetraction (att := att)) :=
  qNew_monotone.comp qBaseStarToBase_monotone

theorem qBaseStarRetraction_le (p : QBaseStar (att := att)) :
    qBaseStarRetraction p ≤ p.1 := by
  rcases p with ⟨p, hp⟩
  cases p with
  | inl c =>
    exact ⟨hp, Finset.nonempty_iff_ne_empty.mpr (fun h => c.2 ⟨h, hp⟩), le_refl _⟩
  | inr x => exact le_refl _

omit [DecidableEq V] in
theorem qBaseStarRetraction_mem_base (p : QBaseStar (att := att)) :
    InQBase (qBaseStarRetraction p) := ⟨qBaseStarToBase p, rfl⟩

omit [DecidableEq V] in
@[simp] theorem qBaseStarRetraction_new (x : X) :
    qBaseStarRetraction (att := att) ⟨qNew x, trivial⟩ = qNew x := rfl

end FiniteChains.Davis
