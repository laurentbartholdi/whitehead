import RequestProject.PresUniversalCockcroftWeakPushdown
import RequestProject.OrderRealizationCockcroft
import RequestProject.PresValidRealization
import RequestProject.TopologicalCockcroftHomotopy

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
variable {α J : Type} [DecidableEq α] [Fintype J]
variable (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

include hw hpos in
/-- The already proved Fox-coordinate Cockcroft property gives the actual
topological property of the presentation realization, without a comparison premise. -/
theorem presRealization_isCockcroft_of_fox (hC : FiniteChains.IsCockcroft ρ) :
    Whitehead.IsCockcroft (orderNerveRealization (PresPos w)) := by
  apply (orderRealization_isCockcroft_iff (ptBase w)
    (presPos_isConnected w (fun j => List.length_pos_iff.mp (hpos j)))).mpr
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H c =>
    change orderNerveH2Map uOrderEnd uOrderEnd_monotone
      (orderNerveH2Class _ c.val c.property) = 0
    rw [orderNerveH2Map_class]
    apply (orderNerveH2Class_eq_zero_iff _ _ _).mpr
    exact ⟨_, (presUniversalCockcroft_weak_pushdown_boundary ρ w hw hpos hC c.val c.property).symm⟩

include hw hpos in
/-- The exact finite-position model retains the actual topological Cockcroft
property established from the presentation's Fox matrix. -/
theorem validPresRealization_isCockcroft_of_fox (hC : FiniteChains.IsCockcroft ρ) :
    Whitehead.IsCockcroft (orderNerveRealization (ValidPresPos w)) :=
  (Whitehead.isCockcroft_iff_of_homotopyEquiv (presValidRealizationHomotopyEquiv w)).mp
    (presRealization_isCockcroft_of_fox ρ w hw hpos hC)

end FiniteChains.PresModel
