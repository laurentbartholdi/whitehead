import RequestProject.MathlibOrderNerveChainBoundary
import RequestProject.OrderNerveH2

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable (P : Type) [PartialOrder P]

/-- The actual Mathlib differential detects precisely the actual cellular two-cycles. -/
theorem mathlibOrderNerve_cycle_iff (c : OrdTri P →₀ ℤ) :
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 1).hom
      (Finsupp.mapDomain (ordTriNerveEquiv P) c) = 0 ↔ FiniteChains.Comb.bdry2 (orderCx P) c = 0 := by
  rw [mathlibOrderNerve_d2]
  constructor
  · intro h
    apply Finsupp.mapDomain_injective (ordEdgeNerveEquiv P).injective
    simpa only [LinearMap.mem_ker, Finsupp.mapDomain_zero] using h
  · intro h
    rw [h, Finsupp.mapDomain_zero]

/-- The actual Mathlib alternating-face two-cycle kernel has genuine order-cell coordinates. -/
noncomputable def mathlibOrderNerveCycleEquiv :
    LinearMap.ker (FiniteChains.Comb.bdry2 (orderCx P)) ≃ₗ[ℤ]
      LinearMap.ker ((AlgebraicTopology.AlternatingFaceMapComplex.objD
        (mathlibOrderNerveModule P) 1).hom) where
  toFun c := ⟨Finsupp.domLCongr (R := ℤ) (M := ℤ) (ordTriNerveEquiv P) c.val,
    by simpa only [LinearMap.mem_ker, Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
      Finsupp.equivMapDomain_eq_mapDomain] using
        (mathlibOrderNerve_cycle_iff P c.val).mpr c.property⟩
  invFun c := ⟨(Finsupp.domLCongr (R := ℤ) (M := ℤ) (ordTriNerveEquiv P)).symm c.val, by
    apply (mathlibOrderNerve_cycle_iff P _).mp
    have he := (Finsupp.domLCongr (R := ℤ) (M := ℤ)
      (ordTriNerveEquiv P)).apply_symm_apply c.val
    simp only [Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
      Finsupp.equivMapDomain_eq_mapDomain] at he
    rw [he]
    exact c.property⟩
  left_inv c := Subtype.ext (LinearEquiv.symm_apply_apply _ c.val)
  right_inv c := Subtype.ext (LinearEquiv.apply_symm_apply _ c.val)
  map_add' c d := Subtype.ext (map_add _ _ _)
  map_smul' n c := Subtype.ext (map_smul _ _ _)

/-- The actual Mathlib three-differential lands in its actual two-cycle kernel. -/
theorem mathlibOrderNerve_d2_d3 (c : CategoryTheory.ComposableArrows P 3 →₀ ℤ) :
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 1).hom
      ((AlgebraicTopology.AlternatingFaceMapComplex.objD
        (mathlibOrderNerveModule P) 2).hom c) = 0 := by
  obtain ⟨d, rfl⟩ := Finsupp.mapDomain_surjective (ordTetNerveEquiv P).surjective c
  rw [mathlibOrderNerve_d3, mathlibOrderNerve_d2, bdry2_ordBoundary3,
    Finsupp.mapDomain_zero]

/-- The actual Mathlib third differential with its genuine cycle-kernel codomain. -/
noncomputable def mathlibOrderNerveBoundary3Cycles :
    (CategoryTheory.ComposableArrows P 3 →₀ ℤ) →ₗ[ℤ]
      LinearMap.ker ((AlgebraicTopology.AlternatingFaceMapComplex.objD
        (mathlibOrderNerveModule P) 1).hom) :=
  ((AlgebraicTopology.AlternatingFaceMapComplex.objD
    (mathlibOrderNerveModule P) 2).hom).codRestrict _ (mathlibOrderNerve_d2_d3 P)

/-- The actual cycle comparison maps precisely onto Mathlib's actual three-boundary range. -/
theorem mathlibOrderNerveCycleEquiv_boundary_range :
    (LinearMap.range (ordBoundary3Cycles P)).map
      (mathlibOrderNerveCycleEquiv P).toLinearMap =
        LinearMap.range (mathlibOrderNerveBoundary3Cycles P) := by
  ext c
  constructor
  · rintro ⟨d, ⟨y, rfl⟩, rfl⟩
    refine ⟨Finsupp.mapDomain (ordTetNerveEquiv P) y, ?_⟩
    apply Subtype.ext
    change _ = (Finsupp.domLCongr (R := ℤ) (M := ℤ)
      (ordTriNerveEquiv P)) (ordBoundary3 y)
    rw [Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
      Finsupp.equivMapDomain_eq_mapDomain]
    exact mathlibOrderNerve_d3 P y
  · rintro ⟨y, rfl⟩
    obtain ⟨d, rfl⟩ := Finsupp.mapDomain_surjective (ordTetNerveEquiv P).surjective y
    refine ⟨ordBoundary3Cycles P d, ⟨d, rfl⟩, ?_⟩
    apply Subtype.ext
    change (Finsupp.domLCongr (R := ℤ) (M := ℤ)
      (ordTriNerveEquiv P)) (ordBoundary3 d) = _
    rw [Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
      Finsupp.equivMapDomain_eq_mapDomain]
    exact (mathlibOrderNerve_d3 P d).symm

/-- Actual order-cell second homology agrees with the quotient formed from
Mathlib's genuine alternating-face differentials. -/
noncomputable def mathlibOrderNerveH2Equiv : OrderNerveH2 P ≃ₗ[ℤ]
    (LinearMap.ker ((AlgebraicTopology.AlternatingFaceMapComplex.objD
      (mathlibOrderNerveModule P) 1).hom)) ⧸
        LinearMap.range (mathlibOrderNerveBoundary3Cycles P) :=
  Submodule.Quotient.equiv _ _ (mathlibOrderNerveCycleEquiv P)
    (mathlibOrderNerveCycleEquiv_boundary_range P)

end FiniteChains.Comb
