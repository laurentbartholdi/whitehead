import RequestProject.OrderConeThreeChains
import RequestProject.PositiveCornerChainExtraction

/-! Actual positive-corner three-fans and their surface extraction. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] (A : CommRel V)

noncomputable def surfaceCornerThreeFan :
    ((orderCx (NeSpx A)).F →₀ ℤ) →ₗ[ℤ] (OrdTet (QCube A) →₀ ℤ) :=
  coneTriangleChain (surfaceFullCube A) (surfaceFullCube_monotone A)
    (positiveCorner A) (positiveCorner_le_surface A)

/-- The explicit positive-corner fan fills every actual surface two-cycle in degree three. -/
theorem surfaceCornerThreeFan_cycle_boundary (c : (orderCx (NeSpx A)).F →₀ ℤ)
    (hc : Comb.bdry2 (orderCx (NeSpx A)) c = 0) :
    ordBoundary3 (surfaceCornerThreeFan A c) =
      chain2 (orderCxMap (surfaceFullCube A) (surfaceFullCube_monotone A)) c :=
  coneTriangleChain_cycle_boundary _ _ _ _ c hc

/-- The actual corner extraction of this three-fan is exactly the original surface chain. -/
theorem cornerSurfaceChain3_surfaceCornerThreeFan (c : (orderCx (NeSpx A)).F →₀ ℤ) :
    cornerSurfaceChain3 A (surfaceCornerThreeFan A c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw (config := { transparency := .default }) [map_add, map_add, hc, hd]
  | single t n =>
      have hlt : positiveCorner A < surfaceFullCube A t.1.1 :=
        (positiveCorner_lt_iff A _).mpr ⟨t.1.1.2.1, rfl⟩
      change chain2 (cornerSurfaceMap A) (cornerChain3 (positiveCorner A)
        (Finsupp.mapDomain (coneTriangleTetrahedron (surfaceFullCube A)
          (surfaceFullCube_monotone A) (positiveCorner A) (positiveCorner_le_surface A))
          (Finsupp.single t n))) = _
      rw (config := { transparency := .default }) [Finsupp.mapDomain_single, cornerChain3, Finsupp.linearCombination_single, map_smul]
      have h : positiveCorner A = positiveCorner A ∧
          positiveCorner A < surfaceFullCube A t.1.1 := ⟨rfl, hlt⟩
      simp only [coneTriangleTetrahedron, cornerTetrahedronTriangle, dif_pos h]
      simp [chain2, cornerSurfaceMap, orderCxMap, positiveCornerLinkEquiv,
        surfaceFullCube, posQCube]

theorem surfaceCornerThreeFan_eq_zero_off_corner
    (c : (orderCx (NeSpx A)).F →₀ ℤ) (t : OrdTet (QCube A))
    (ht : t.1.1 ≠ positiveCorner A) : surfaceCornerThreeFan A c t = 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw (config := { transparency := .default }) [map_add, Finsupp.add_apply, hc, hd, add_zero]
  | single s n =>
      have he : coneTriangleTetrahedron (surfaceFullCube A) (surfaceFullCube_monotone A)
          (positiveCorner A) (positiveCorner_le_surface A) s ≠ t := by
        intro h
        exact ht (congrArg (fun t : OrdTet (QCube A) => t.1.1) h).symm
      change Finsupp.mapDomain _ (Finsupp.single s n) t = 0
      rw (config := { transparency := .default }) [Finsupp.mapDomain_single]
      exact Finsupp.single_eq_of_ne (Ne.symm he)

end FiniteChains.Davis
