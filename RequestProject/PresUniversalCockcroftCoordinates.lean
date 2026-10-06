module

public import RequestProject.PresUniversalRelatorAugmentation

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} [DecidableEq α] [Fintype J]
  (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

/-- Genuine geometric kernel coordinates satisfy the actual Fox-cycle equations. -/
theorem presUniversalRelatorRingEquiv_isFoxCycle
    (c : PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w)) →₀ ℤ)
    (hc : presCoverRelatorGeneratorBoundary (P := UOrder (PresPos w) (ptBase w))
      w uOrderEnd (presUniversalEnd_isPosetCover w hpos) c = 0) :
    IsFoxCycle ρ (presUniversalRelatorRingEquiv ρ w hw hpos c) := by
  have h := presUniversalFox_coordinates_commute ρ w hw hpos c
  rw [hc, map_zero] at h
  intro i
  have hi := congrArg (fun v => v i) h.symm
  simpa [coverSecondBoundary, Finsupp.linearCombination_apply, Finsupp.sum_fintype,
    Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul,
    coverFoxGradient, Finsupp.mapRange_apply, foxGradient_apply, foxMatrixPres,
    Finsupp.zero_apply, proj, quotRingHom] using hi

include hw in
/-- Cockcroft presentations have zero base relator coefficients on genuine universal two-cycles. -/
theorem presUniversalCockcroft_relator_augmentation_zero
    (hC : IsCockcroft ρ)
    (c : LinearMap.ker (Comb.bdry2 (strictOrderCx (UOrder (PresPos w) (ptBase w))))) :
    Finsupp.mapDomain (fun p => p.val.2)
      (presCoverRelatorChain w uOrderEnd (presUniversalEnd_isPosetCover w hpos) hpos c.val) = 0 := by
  let he := presCoverCycleRelatorGeneratorKernelEquiv w uOrderEnd
    (presUniversalEnd_isPosetCover w hpos) hpos c
  have hfox := presUniversalRelatorRingEquiv_isFoxCycle ρ w hw hpos he.val he.property
  ext j
  rw [← presUniversalRelatorRingEquiv_augmentation ρ w hw hpos]
  have hz := hC _ hfox j
  change augQ (relSub ρ) (presUniversalRelatorRingEquiv ρ w hw hpos he.val j) = 0 at hz
  exact hz

end FiniteChains.PresModel
