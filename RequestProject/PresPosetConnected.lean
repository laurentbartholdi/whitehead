import RequestProject.OrderConstructionConnected
import RequestProject.PresPosetNonemptyWords

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u}

theorem rose_isConnected : IsConnected (orderCx (Rose α)) := by
  have h : ∀ x : Rose α, orderComponentLabel _ x = orderComponentLabel _ Rose.base := by
    intro x
    cases x with
    | base => rfl
    | mid i =>
        exact (orderComponentLabel_eq_of_le (Rose.mid_le_edg i false)).trans
          (orderComponentLabel_eq_of_le (Rose.base_le_edg i false)).symm
    | edg i b => exact (orderComponentLabel_eq_of_le (Rose.base_le_edg i b)).symm
  intro x y
  exact (orderComponentLabel_eq_iff _ _).mp ((h x).trans (h y).symm)

/-- Nonempty attaching words give connected genuine presentation poset models. -/
theorem presPos_isConnected (w : J → List (α × Bool)) (hw : ∀ j, w j ≠ []) :
    IsConnected (orderCx (PresPos w)) := by
  apply coneAdj_isConnected (circSet w)
    (cylP_isConnected (aHom w) rose_isConnected)
  intro j
  exact ⟨cylOuter (aHom w) (TCirc.pt w j 0 CPos.cor),
    0, CPos.cor, List.length_pos_iff.mpr (hw j), rfl⟩

theorem presNonemptyWords_isConnected (ρ : J → FreeGroup α) (a : α) :
    IsConnected (orderCx (PresPos (presNonemptyWords ρ a))) :=
  presPos_isConnected _ (presNonemptyWords_ne_nil ρ a)

end FiniteChains.PresModel
