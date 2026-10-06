import RequestProject.OrderUniversalH2Equiv
import RequestProject.PresUniversalFoxHomologyEquiv

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} [DecidableEq α]
  (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

/-- Actual lifted-order second homology has the actual presentation's Fox kernel coordinates. -/
noncomputable def presOrderNerveFoxH2Equiv :
    OrderNerveH2 (UOrder (PresPos w) (ptBase w)) ≃ₗ[ℤ]
      LinearMap.ker ((coverSecondBoundary (relSub ρ) ρ).restrictScalars ℤ) :=
  uOrderH2Equiv.trans (presUniversalCycleQuotientFoxKernelEquiv ρ w hw hpos)

/-- The homology/Fox comparison reads the actual path-cover chain of each lifted-order cycle. -/
theorem presOrderNerveFoxH2Equiv_class
    (c : OrdTri (UOrder (PresPos w) (ptBase w)) →₀ ℤ)
    (hc : Comb.bdry2 (orderCx (UOrder (PresPos w) (ptBase w))) c = 0) :
    (presOrderNerveFoxH2Equiv ρ w hw hpos
      (orderNerveH2Class _ c hc)).val =
      presUniversalRelatorRingEquiv ρ w hw hpos
        (presUniversalRelatorCoordinates w hpos (uOrderChain2Equiv c)) := by
  exact presUniversalCycleQuotientFoxKernelEquiv_mk ρ w hw hpos
    (uOrderCycleEquiv ⟨c, hc⟩)

end FiniteChains.PresModel
