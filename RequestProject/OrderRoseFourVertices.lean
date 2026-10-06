module

public import RequestProject.OrderRoseWedgeTopology

@[expose] public section

/-! The concrete cyclic order of the four vertices in one rose circle.
This fixes the positive generator orientation before passing to realization. -/

noncomputable section
namespace FiniteChains.PresModel
open scoped Classical

def roseFourVertex : Fin 4 → Rose PUnit :=
  ![.base, .edg PUnit.unit false, .mid PUnit.unit, .edg PUnit.unit true]

theorem roseFourVertex_injective : Function.Injective roseFourVertex := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [roseFourVertex]

theorem roseFourVertex_surjective : Function.Surjective roseFourVertex := by
  intro p
  cases p with
  | base => exact ⟨0, rfl⟩
  | mid a => cases a; exact ⟨2, rfl⟩
  | edg a b =>
      cases a
      cases b
      · exact ⟨1, rfl⟩
      · exact ⟨3, rfl⟩

def roseFourVertexEquiv : Fin 4 ≃ Rose PUnit :=
  Equiv.ofBijective roseFourVertex ⟨roseFourVertex_injective, roseFourVertex_surjective⟩

theorem roseFourVertex_comparable_iff (i j : Fin 4) :
    (roseFourVertex i ≤ roseFourVertex j ∨ roseFourVertex j ≤ roseFourVertex i) ↔
      i = j ∨ (i.val + 1) % 4 = j.val ∨ (j.val + 1) % 4 = i.val := by
  change (Rose.le (roseFourVertex i) (roseFourVertex j) ∨
    Rose.le (roseFourVertex j) (roseFourVertex i)) ↔ _
  fin_cases i <;> fin_cases j <;> norm_num [roseFourVertex, Rose.le]

@[simp] theorem roseFourVertex_zero : roseFourVertex 0 = Rose.base := rfl

end FiniteChains.PresModel
