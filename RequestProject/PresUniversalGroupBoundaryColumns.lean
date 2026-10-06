module

public import RequestProject.PresUniversalLetterGroupCoordinates
public import RequestProject.PresUniversalRelatorGroupCoordinates

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

/-- The genuine universal relator boundary expressed in actual group coordinates. -/
noncomputable def presUniversalGroupBoundary :
    (PresGroup ρ × J →₀ ℤ) →ₗ[ℤ] (PresGroup ρ × α →₀ ℤ) :=
  (presUniversalGeneratorGroupChainEquiv ρ w hw hpos).toLinearMap.comp
    ((presCoverRelatorGeneratorBoundary (P := UOrder (PresPos w) (ptBase w)) w uOrderEnd
      (presUniversalEnd_isPosetCover w hpos)).comp
        (presUniversalRelatorGroupChainEquiv ρ w hw hpos).symm.toLinearMap)

/-- An actual relator boundary column is the sum of its signed prefix group-generator incidences. -/
theorem presUniversalGroupBoundary_actual_column
    (p : PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w))) :
    presUniversalGroupBoundary ρ w hw hpos
      (Finsupp.single (presUniversalRelatorGroupEquiv ρ w hw hpos p) 1) =
      ∑ k : Fin (w p.val.2).length,
        (if ((w p.val.2)[k.val]).2 then (1 : ℤ) else -1) •
          Finsupp.single
            ((presGroupCocycle ρ w hw).readVertex (ptBase w) p.val.1 *
              (prefixVal w (fun i => (QuotientGroup.mk (FreeGroup.of i) : PresGroup ρ))
                p.val.2 k.val *
                (if ((w p.val.2)[k.val]).2 then 1 else
                  (QuotientGroup.mk (FreeGroup.of ((w p.val.2)[k.val]).1) : PresGroup ρ)⁻¹)),
              ((w p.val.2)[k.val]).1) 1 := by
  classical
  simp only [presUniversalGroupBoundary, LinearMap.comp_apply,
    LinearEquiv.coe_coe, presUniversalRelatorGroupChainEquiv,
    Finsupp.domLCongr_symm, Finsupp.domLCongr_single, Equiv.symm_apply_apply]
  rw [presCoverRelatorGeneratorBoundary_single]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul]
  congr 1
  rw [presUniversalGeneratorGroupChainEquiv, Finsupp.domLCongr_single,
    presUniversalGeneratorGroupEquiv_midpoint, presUniversalLetter_midpoint_coordinates]

end FiniteChains.PresModel
