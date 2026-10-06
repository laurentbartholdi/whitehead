module

public import RequestProject.Fox

@[expose] public section

namespace FiniteChains
variable {α : Type*} [DecidableEq α]

/-- The group element read by one oriented letter. -/
def foxWordLetter (p : α × Bool) : FreeGroup α :=
  if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹

/-- The signed contribution of an oriented generator edge to its Fox coordinate. -/
noncomputable def foxWordIncidence (i : α) (p : α × Bool) : FreeGroupRing α :=
  if i = p.1 then (if p.2 then 1 else -grp (FreeGroup.of p.1)⁻¹) else 0

omit [DecidableEq α] in
theorem fox_mk_single_letter (p : α × Bool) :
    FreeGroup.mk [p] = foxWordLetter p := by
  obtain ⟨a, b⟩ := p
  cases b
  · change FreeGroup.mk [(a, false)] = (FreeGroup.of a)⁻¹
    rw [show FreeGroup.of a = FreeGroup.mk [(a, true)] from rfl, FreeGroup.inv_mk]
    rfl
  · rfl

theorem fox_letter_incidence (i : α) (p : α × Bool) :
    fox i (foxWordLetter p) = foxWordIncidence i p := by
  obtain ⟨a, b⟩ := p
  cases b <;> by_cases h : i = a <;>
    simp [foxWordLetter, foxWordIncidence, fox_inv, h]

/-- The actual signed edge sum of a word path, starting at the translate `g`.
Negative letters contribute at the terminal generator coordinate. -/
noncomputable def foxWordPathBoundary (i : α) (g : FreeGroup α) :
    List (α × Bool) → FreeGroupRing α
  | [] => 0
  | p :: l => grp g * foxWordIncidence i p +
      foxWordPathBoundary i (g * foxWordLetter p) l

/-- The signed edge sum equals the translated Fox derivative of the actual word. -/
theorem foxWordPathBoundary_eq (i : α) (g : FreeGroup α) (l : List (α × Bool)) :
    foxWordPathBoundary i g l = grp g * fox i (FreeGroup.mk l) := by
  induction l generalizing g with
  | nil => simp [foxWordPathBoundary, ← FreeGroup.one_eq_mk]
  | cons p l ih =>
    have hm : FreeGroup.mk (p :: l) = foxWordLetter p * FreeGroup.mk l := by
      rw [← fox_mk_single_letter, FreeGroup.mul_mk]
      rfl
    rw [foxWordPathBoundary, ih, hm, fox_mul, fox_letter_incidence, grp_mul,
      mul_add, mul_assoc]

/-- Concatenating actual word paths adds their signed boundaries at the actual endpoint. -/
theorem foxWordPathBoundary_append (i : α) (g : FreeGroup α)
    (l r : List (α × Bool)) :
    foxWordPathBoundary i g (l ++ r) =
      foxWordPathBoundary i g l + foxWordPathBoundary i (g * FreeGroup.mk l) r := by
  rw [foxWordPathBoundary_eq, foxWordPathBoundary_eq, foxWordPathBoundary_eq,
    ← FreeGroup.mul_mk, fox_mul, grp_mul, mul_add, mul_assoc]

/-- At the identity vertex, the word edge sum is exactly the Fox boundary entry. -/
theorem foxWordPathBoundary_one (i : α) (l : List (α × Bool)) :
    foxWordPathBoundary i 1 l = fox i (FreeGroup.mk l) := by
  rw [foxWordPathBoundary_eq, grp_one, one_mul]

end FiniteChains
