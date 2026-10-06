module

public import RequestProject.PresUniversalGeneratorGroupCoordinates
public import RequestProject.PresCoverRelatorLetterCoefficients
public import RequestProject.PresUniversalCylinderCollapseReading

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

/-- The actual lifted-letter midpoint coordinates are exactly the signed prefix coordinates. -/
theorem presUniversalLetter_midpoint_coordinates
    (p : PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w)))
    (k : Fin (w p.val.2).length) :
    presUniversalMidpointGroupEquiv ρ w hw hpos
      (presCoverRelatorLetterMidpoint (P := UOrder (PresPos w) (ptBase w)) w uOrderEnd
        (presUniversalEnd_isPosetCover w hpos) p k) =
      ((presGroupCocycle ρ w hw).readVertex (ptBase w) p.val.1 *
        (prefixVal w (fun i => (QuotientGroup.mk (FreeGroup.of i) : PresGroup ρ))
          p.val.2 k.val *
          (if ((w p.val.2)[k.val]).2 then 1 else
            (QuotientGroup.mk (FreeGroup.of ((w p.val.2)[k.val]).1) : PresGroup ρ)⁻¹)),
        ((w p.val.2)[k.val]).1) := by
  apply Prod.ext
  · exact presUniversalRelator_collapsed_midpoint_reading w hpos
      (fun i => (QuotientGroup.mk (FreeGroup.of i) : PresGroup ρ))
      (presGroup_wordVal_eq_one ρ w hw) p k
  · rfl

/-- The selected incidence of an actual midpoint has that midpoint's group coordinates. -/
theorem presUniversalGeneratorGroupEquiv_midpoint
    (m : roseCoverMidpoints (cylinderCoverRoseEnd w
      (coneAdjCoverBaseEnd (uOrderEnd (P := PresPos w) (a := ptBase w))))) :
    presUniversalGeneratorGroupEquiv ρ w hw hpos
      (roseCoverMidpointEdge _ (cylinderCoverRoseEnd_isPosetCover w _
        (coneAdjCoverBaseEnd_isPosetCover _ (presUniversalEnd_isPosetCover w hpos))) m) =
      presUniversalMidpointGroupEquiv ρ w hw hpos m := by
  change presUniversalMidpointGroupEquiv ρ w hw hpos
    ((roseCoverMidpointEdgeEquiv _ (cylinderCoverRoseEnd_isPosetCover w _
      (coneAdjCoverBaseEnd_isPosetCover _ (presUniversalEnd_isPosetCover w hpos)))).symm
      ((roseCoverMidpointEdgeEquiv _ (cylinderCoverRoseEnd_isPosetCover w _
        (coneAdjCoverBaseEnd_isPosetCover _ (presUniversalEnd_isPosetCover w hpos)))) m)) = _
  rw [Equiv.symm_apply_apply]

end FiniteChains.PresModel
