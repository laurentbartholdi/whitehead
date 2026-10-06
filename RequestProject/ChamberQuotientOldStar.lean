import RequestProject.ChamberQuotientCycleGeneration

/-! The quotient is an unmixed union of its actual old cells and the inserted-base star. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

def InQOld : Qpos A X att → Prop
  | .inl _ => True
  | .inr _ => False

def InQBaseStar : Qpos A X att → Prop
  | .inl c => c.1.sgn = 0
  | .inr _ => True

omit [DecidableEq V] in
theorem inQBase_in_star {p : Qpos A X att} (hp : InQBase p) : InQBaseStar p := by
  obtain ⟨x, rfl⟩ := hp
  trivial

omit [DecidableEq V] in
theorem qOld_baseStar_cover (p : Qpos A X att) : InQOld p ∨ InQBaseStar p := by
  cases p with
  | inl c => exact Or.inl trivial
  | inr x => exact Or.inr trivial

theorem qOld_baseStar_unmixed (p r : Qpos A X att) (h : p ≤ r) :
    (InQOld p ∧ InQOld r) ∨ (InQBaseStar p ∧ InQBaseStar r) := by
  cases p with
  | inl c =>
    cases r with
    | inl d => exact Or.inl ⟨trivial, trivial⟩
    | inr y => exact False.elim h
  | inr x =>
    cases r with
    | inl d => exact Or.inr ⟨trivial, h.1⟩
    | inr y => exact Or.inr ⟨trivial, trivial⟩

omit [DecidableEq V] in
/-- The intersection consists exactly of the positive retained cubes,
the actual copy of the attaching simplex poset. -/
theorem qOld_baseStar_intersection (p : Qpos A X att) :
    InQOld p ∧ InQBaseStar p ↔ ∃ c : QOld A, p = Sum.inl c ∧ c.1.sgn = 0 := by
  cases p with
  | inl c =>
    constructor
    · exact fun h => ⟨c, rfl, h.2⟩
    · rintro ⟨d, he, hd⟩
      cases Sum.inl.inj he
      exact ⟨trivial, hd⟩
  | inr x => simp [InQOld]

end FiniteChains.Davis
