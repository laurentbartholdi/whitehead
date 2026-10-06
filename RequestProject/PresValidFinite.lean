import RequestProject.PresValidPoset
import RequestProject.PresPosetDimension
import RequestProject.OrderNerveDimension
import RequestProject.OrderNerveRealizationFinite

namespace FiniteChains.PresModel
open Comb CategoryTheory
universe u

instance cPos_finite : Finite CPos := by
  let index : CPos → Fin 4
    | .cor => 0
    | .cmid => 1
    | .cedgL => 2
    | .cedgR => 3
  exact Finite.of_injective index (by
    intro a b h
    cases a <;> cases b <;> simp_all [index])

instance rose_finite {α : Type u} [Finite α] : Finite (Rose α) := by
  let decode : Option (α × Option Bool) → Rose α
    | none => .base
    | some (a, none) => .mid a
    | some (a, some b) => .edg a b
  apply Finite.of_surjective decode
  intro r
  cases r with
  | base => exact ⟨none, rfl⟩
  | mid a => exact ⟨some (a, none), rfl⟩
  | edg a b => exact ⟨some (a, some b), rfl⟩

variable {α J : Type u} (w : J → List (α × Bool))

/-- Actual word positions have bounded finite indices, even though the old model
uses all natural numbers for its unused positions. -/
instance validPresPos_finite [Finite α] [Finite J] : Finite (ValidPresPos w) := by
  let decode : Rose α ⊕ ((Σ j : J, Fin (w j).length × CPos) ⊕ J) → ValidPresPos w
    | .inl r => ⟨iRose w r, trivial⟩
    | .inr (.inl ⟨j, k, t⟩) => ⟨iCirc w (TCirc.pt w j k.val t), k.isLt⟩
    | .inr (.inr j) => ⟨apexOf w j, trivial⟩
  apply Finite.of_surjective decode
  rintro ⟨p, hp⟩
  cases p with
  | inl p =>
    cases p with
    | inl r => exact ⟨.inl r, rfl⟩
    | inr c =>
      obtain ⟨j, k, t⟩ := c
      exact ⟨.inr (.inl ⟨j, ⟨k, hp⟩, t⟩), rfl⟩
  | inr j => exact ⟨.inr (.inr j), rfl⟩

instance validPresPos_hasDimensionLE : (nerve (ValidPresPos w)).HasDimensionLE 2 :=
  orderNerve_hasDimensionLE (fun p : ValidPresPos w => presPosDimension w p.val)
    ((presPosDimension_strictMono w).comp (fun _ _ h => h)) 2
    (fun p => presPosDimension_le_two w p.val)

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb CategoryTheory
variable {α J : Type} (w : J → List (α × Bool))

/-- The reduced model is a genuine connected two-dimensional CW complex. -/
noncomputable def validPresTwoComplex (hw : ∀ j, w j ≠ []) : Whitehead.TwoComplex :=
  orderNerveTwoComplex (ValidPresPos w) (validPresPos_isConnected w hw)

/-- Finite presentations now give the actual finite-cell property from Challenge. -/
theorem validPresTwoComplex_finiteCells [Finite α] [Finite J] (hw : ∀ j, w j ≠ []) :
    Whitehead.FiniteCells (validPresTwoComplex w hw) :=
  orderNerveTwoComplex_finiteCells (ValidPresPos w) (validPresPos_isConnected w hw)

end FiniteChains.PresModel
