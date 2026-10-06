import RequestProject.PresUniversalRelatorHomology

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

/-- The genuine lifted three-boundary with codomain its actual cover two-cycle kernel. -/
noncomputable def uOrdBoundary3Cycles : (UOrdTet P a →₀ ℤ) →ₗ[ℤ]
    LinearMap.ker (bdry2 (uCover (orderCx P) a)) :=
  (uOrdBoundary3 (P := P) (a := a)).codRestrict
    (LinearMap.ker (bdry2 (uCover (orderCx P) a)))
    (fun y => LinearMap.mem_ker.mpr (bdry2_uOrdBoundary3 y))
end FiniteChains.Comb

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool))
  (hpos : ∀ j, 0 < (w j).length)

/-- The actual finite relator-coordinate linear map restricted to genuine cover cycles. -/
noncomputable def presUniversalCycleRelatorCoordinates :
    LinearMap.ker (Comb.bdry2 (uCover (orderCx (PresPos w)) (ptBase w))) →ₗ[ℤ]
      (PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w)) →₀ ℤ) :=
  (presUniversalRelatorCoordinates w hpos).comp
    (LinearMap.ker (Comb.bdry2 (uCover (orderCx (PresPos w)) (ptBase w)))).subtype

/-- The kernel of the actual cycle-coordinate map is exactly the actual three-boundary range. -/
theorem presUniversalCycleRelatorCoordinates_ker :
    LinearMap.ker (presUniversalCycleRelatorCoordinates w hpos) =
      LinearMap.range (uOrdBoundary3Cycles (P := PresPos w) (a := ptBase w)) := by
  ext c
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hc
    obtain ⟨y, hy⟩ := (presUniversalRelatorCoordinates_zero_iff_boundary w hpos c.val
      (LinearMap.mem_ker.mp c.property)).mp hc
    exact ⟨y, Subtype.ext hy⟩
  · rintro ⟨y, rfl⟩
    exact presUniversalRelatorCoordinates_boundary_zero w hpos y

/-- The actual cycle module modulo actual lifted three-boundaries is linearly
identified with the range of its proved finite relator coordinates. -/
noncomputable def presUniversalCycleQuotientRelatorEquiv :
    (LinearMap.ker (Comb.bdry2 (uCover (orderCx (PresPos w)) (ptBase w))) ⧸
      LinearMap.range (uOrdBoundary3Cycles (P := PresPos w) (a := ptBase w))) ≃ₗ[ℤ]
        LinearMap.range (presUniversalCycleRelatorCoordinates w hpos) :=
  (Submodule.quotEquivOfEq _ _ (presUniversalCycleRelatorCoordinates_ker w hpos).symm).trans
    (presUniversalCycleRelatorCoordinates w hpos).quotKerEquivRange

theorem presUniversalCycleQuotientRelatorEquiv_mk
    (c : LinearMap.ker (Comb.bdry2 (uCover (orderCx (PresPos w)) (ptBase w)))) :
    (presUniversalCycleQuotientRelatorEquiv w hpos (Submodule.Quotient.mk c)).val =
      presUniversalRelatorCoordinates w hpos c.val := by
  simp [presUniversalCycleQuotientRelatorEquiv, LinearEquiv.trans_apply,
    presUniversalCycleRelatorCoordinates]
  rfl

end FiniteChains.PresModel
