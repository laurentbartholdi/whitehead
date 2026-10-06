import RequestProject.PresUniversalFoxKernelEquiv
import RequestProject.PresUniversalCollapsedKernelEquiv

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} [DecidableEq α] (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

/-- Actual universal-cover two-cycle classes modulo actual three-boundaries
have the genuine algebraic Fox kernel coordinates. -/
noncomputable def presUniversalCycleQuotientFoxKernelEquiv :
    (LinearMap.ker (Comb.bdry2 (uCover (orderCx (PresPos w)) (ptBase w))) ⧸
      LinearMap.range (uOrdBoundary3Cycles (P := PresPos w) (a := ptBase w))) ≃ₗ[ℤ]
        LinearMap.ker ((coverSecondBoundary (relSub ρ) ρ).restrictScalars ℤ) :=
  (presUniversalCycleQuotientCollapsedKernelEquiv w hpos).trans
    ((LinearEquiv.ofEq _ _ (presCoverCollapsedRelatorBoundary_ker_eq_generator w uOrderEnd
      (presUniversalEnd_isPosetCover w hpos))).trans
        (presUniversalGeneratorFoxKernelEquiv ρ w hw hpos))

/-- The actual quotient/Fox comparison reads a cycle's actual finite relator coordinates. -/
theorem presUniversalCycleQuotientFoxKernelEquiv_mk
    (c : LinearMap.ker (Comb.bdry2 (uCover (orderCx (PresPos w)) (ptBase w)))) :
    (presUniversalCycleQuotientFoxKernelEquiv ρ w hw hpos (Submodule.Quotient.mk c)).val =
      presUniversalRelatorRingEquiv ρ w hw hpos
        (presUniversalRelatorCoordinates w hpos c.val) := by
  change presUniversalRelatorRingEquiv ρ w hw hpos
    (presUniversalCycleQuotientCollapsedKernelEquiv w hpos (Submodule.Quotient.mk c)).val = _
  rw [presUniversalCycleQuotientCollapsedKernelEquiv_mk]

end FiniteChains.PresModel
