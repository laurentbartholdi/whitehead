import RequestProject.PresUniversalGroupBoundaryColumns
import RequestProject.GroupCellChainCoordinates

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

/-- The actual universal boundary in group-ring cell coordinates. -/
noncomputable def presUniversalGroupRingBoundary :
    (J →₀ MonoidAlgebra ℤ (PresGroup ρ)) →ₗ[ℤ]
      (α →₀ MonoidAlgebra ℤ (PresGroup ρ)) :=
  groupCellChainEquiv.toLinearMap.comp
    ((presUniversalGroupBoundary ρ w hw hpos).comp groupCellChainEquiv.symm.toLinearMap)

/-- Actual geometric columns in generator-indexed group-ring coefficients. -/
theorem presUniversalGroupRingBoundary_actual_column
    (p : PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w))) :
    presUniversalGroupRingBoundary ρ w hw hpos
      (Finsupp.single p.val.2 (MonoidAlgebra.single
        ((presGroupCocycle ρ w hw).readVertex (ptBase w) p.val.1) 1)) =
      ∑ k : Fin (w p.val.2).length,
        (if ((w p.val.2)[k.val]).2 then (1 : ℤ) else -1) •
          Finsupp.single ((w p.val.2)[k.val]).1
            (MonoidAlgebra.single
              ((presGroupCocycle ρ w hw).readVertex (ptBase w) p.val.1 *
                ((QuotientGroup.mk (FreeGroup.mk ((w p.val.2).take k.val)) : PresGroup ρ) *
                  (if ((w p.val.2)[k.val]).2 then 1 else
                    (QuotientGroup.mk (FreeGroup.of ((w p.val.2)[k.val]).1) : PresGroup ρ)⁻¹))) 1) := by
  classical
  have hs := groupCellChainEquiv_single
    ((presGroupCocycle ρ w hw).readVertex (ptBase w) p.val.1) p.val.2 (1 : ℤ)
  rw [← hs]
  change groupCellChainEquiv (presUniversalGroupBoundary ρ w hw hpos
    (groupCellChainEquiv.symm (groupCellChainEquiv
      (Finsupp.single (presUniversalRelatorGroupEquiv ρ w hw hpos p) 1)))) = _
  rw [LinearEquiv.symm_apply_apply, presUniversalGroupBoundary_actual_column, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul, groupCellChainEquiv_single]
  congr 3
  rw [prefixVal, presGroup_wordVal]

end FiniteChains.PresModel
