module

public import RequestProject.OrderNerveLowerCone
public import RequestProject.RelatorCircleBoundaryHomeomorph

@[expose] public section

/-! The actual closed lower ideal of a nonempty relator apex is a genuine
two-dimensional disk. Its strict lower interval is precisely the norm-one
boundary, with the fixed relator-circle parametrization. -/

noncomputable section
namespace FiniteChains.PresModel
open Comb RelativeAttachment
open scoped Classical

variable {α J : Type} (w : J → List (α × Bool)) (j : J)
    (hn : 0 < (w j).length)

noncomputable instance relatorCircle_fintype : Fintype (RelatorCircle w j) :=
  Fintype.ofFinite _

def presConeBallHomeomorph :
    orderNerveRealization (Set.Iic (apexOf w j)) ≃ₜ ClosedUnitBall (Fin 2 → ℝ) := by
  letI : Nonempty (RelatorCircle w j) := relatorCircle_nonempty w j (List.ne_nil_of_length_pos hn)
  exact lowerConeBallHomeomorph (apexOf w j) (relatorCircleOrderIso w j)
    (relatorCircleBoundaryHomeomorph w j hn)

theorem presConeBallHomeomorph_boundary (x : orderNerveRealization (RelatorCircle w j)) :
    presConeBallHomeomorph w j hn
      (orderNerveRealizationMap (lowerConeBoundary (apexOf w j) (relatorCircleOrderIso w j))
        (lowerConeBoundary (apexOf w j) (relatorCircleOrderIso w j)).monotone x) =
      unitBoundaryInclusion (Fin 2 → ℝ) (relatorCircleBoundaryHomeomorph w j hn x) := by
  letI : Nonempty (RelatorCircle w j) := relatorCircle_nonempty w j (List.ne_nil_of_length_pos hn)
  exact lowerConeBallHomeomorph_boundary _ _ _ x

theorem presConeBallHomeomorph_boundary_iff (x : orderNerveRealization (Set.Iic (apexOf w j))) :
    ‖(presConeBallHomeomorph w j hn x).val‖ = 1 ↔
      x ∈ Set.range (orderNerveRealizationMap
        (lowerConeBoundary (apexOf w j) (relatorCircleOrderIso w j))
        (lowerConeBoundary (apexOf w j) (relatorCircleOrderIso w j)).monotone) := by
  letI : Nonempty (RelatorCircle w j) := relatorCircle_nonempty w j (List.ne_nil_of_length_pos hn)
  exact lowerConeBallHomeomorph_boundary_iff _ _ _ x

end FiniteChains.PresModel
