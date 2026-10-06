module

public import RequestProject.PresUniversalGroupCoordinates
public import RequestProject.PresCoverRelatorChains
public import RequestProject.OrderUniversalPoset

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

/-- Actual lifted relators are indexed by their apex reading and actual relator label. -/
noncomputable def presUniversalRelatorGroupEquiv :
    PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w)) ≃ PresGroup ρ × J where
  toFun p := ((presGroupCocycle ρ w hw).readVertex (ptBase w) p.val.1, p.val.2)
  invFun q :=
    let p := (presUniversalFibreGroupEquiv ρ w hw hpos (apexOf w q.2)).symm q.1
    ⟨(p.val, q.2), p.property⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val
        ((presUniversalFibreGroupEquiv ρ w hw hpos (apexOf w p.val.2)).symm_apply_apply
          ⟨p.val.1, p.property⟩)
    · rfl
  right_inv q := by
    apply Prod.ext
    · exact (presUniversalFibreGroupEquiv ρ w hw hpos (apexOf w q.2)).apply_symm_apply q.1
    · rfl

/-- Finite actual relator coefficients expressed in actual presentation-group coordinates. -/
noncomputable def presUniversalRelatorGroupChainEquiv :
    (PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w)) →₀ ℤ) ≃ₗ[ℤ]
      (PresGroup ρ × J →₀ ℤ) :=
  Finsupp.domLCongr (R := ℤ) (M := ℤ) (presUniversalRelatorGroupEquiv ρ w hw hpos)

end FiniteChains.PresModel
