import RequestProject.CubicalThreeBoundaryMatrix

/-! The genuine finite oriented six-face boundary chain. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis

noncomputable def threeOrientedFaces : (Fin 3 × ZMod 2) →₀ ℤ :=
  Finsupp.single (0, 0) 1 - Finsupp.single (0, 1) 1 -
  Finsupp.single (1, 0) 1 + Finsupp.single (1, 1) 1 +
  Finsupp.single (2, 0) 1 - Finsupp.single (2, 1) 1

theorem threeOrientedFaces_apply (i : Fin 3 × ZMod 2) :
    threeOrientedFaces i = threeFacetOrientation i := by
  obtain ⟨e, s⟩ := i
  fin_cases e <;> fin_cases s <;>
    norm_num [threeOrientedFaces, threeFacetOrientation, fixedCoordinateSign, Fin.ext_iff,
      Finsupp.single_apply, Prod.mk.injEq]

theorem threeFacetBoundaryMatrix_kernel_chain (r : (Fin 3 × ZMod 2) →₀ ℤ)
    (hr : threeFacetBoundaryMatrix r = 0) : r = r (0, 0) • threeOrientedFaces := by
  ext i
  rw [Finsupp.smul_apply, threeOrientedFaces_apply, threeFacetBoundaryMatrix_kernel r hr i]
  rfl

end FiniteChains.Davis
