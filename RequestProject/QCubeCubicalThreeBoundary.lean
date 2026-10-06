module

public import RequestProject.QCubeThreeBoundaryRecovery

@[expose] public section

/-! Actual cubical three-to-two boundary and its finite strict subdivision dictionary. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

noncomputable def qThreeCubicalFaceBoundary (c : QThreeCube A) : QSquare A →₀ ℤ :=
  Finsupp.lmapDomain ℤ ℤ
    (qThreeFaceSquare c.1 (qThreeUpper c) (qThreeMiddle c) (qThreeLower c)
      (Ne.symm (qThree_middle_lt_upper c).ne)
      (Ne.symm ((qThree_lower_lt_middle c).trans (qThree_middle_lt_upper c)).ne)
      (Ne.symm (qThree_lower_lt_middle c).ne) (qThree_free_directions c)) threeOrientedFaces

noncomputable def qThreeCubicalBoundary : (QThreeCube A →₀ ℤ) →ₗ[ℤ]
    (QSquare A →₀ ℤ) := Finsupp.linearCombination ℤ qThreeCubicalFaceBoundary

theorem qThreeCubicalFaceBoundary_subdivision (c : QThreeCube A) :
    qSquareChainSubdivision (qThreeCubicalFaceBoundary c) = qThreeCubeBoundary c :=
  qThreeOrientedFaces_subdivision c.1 _ _ _ (qThree_middle_lt_upper c)
    (qThree_lower_lt_middle c) (qThree_free_directions c)

theorem qThreeCubicalBoundary_subdivision (r : QThreeCube A →₀ ℤ) :
    qSquareChainSubdivision (qThreeCubicalBoundary r) = qThreeChainBoundary r := by
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s hr hs => rw [map_add, map_add, hr, hs, map_add]
  | single c n =>
      rw [qThreeCubicalBoundary, Finsupp.linearCombination_single, map_smul,
        qThreeCubicalFaceBoundary_subdivision, qThreeChainBoundary,
        Finsupp.linearCombination_single]

theorem qThreeCubicalBoundary_squared (r : QThreeCube A →₀ ℤ) :
    qSquareCubicalBoundary (qThreeCubicalBoundary r) = 0 := by
  apply (qSquareCubicalBoundary_zero_iff _).mpr
  have hnat : Comb.bdry2 (strictOrderCx (QCube A))
      (qSquareChainSubdivision (qThreeCubicalBoundary r)) =
      qSquareFacetBoundary (qThreeCubicalBoundary r) :=
    squareChainSubdivision_boundary Subtype.val qSquareLeft qSquareRight
      qSquare_directions_ne qSquare_free_directions _
  rw [← hnat, qThreeCubicalBoundary_subdivision, qThreeChainBoundary_cycle]

/-- Every strict three-boundary with the stated actual dimension bounds is the subdivision
of an actual finite cubical three-boundary, and coefficient recovery gives that boundary. -/
theorem qCube_three_cubical_boundary_reconstruction (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2) :
    ∃ r : QThreeCube A →₀ ℤ,
      qSquareChainSubdivision (qThreeCubicalBoundary r) = strictOrdBoundary3 y ∧
      qSquareCycleCoefficients (strictOrdBoundary3 y) = qThreeCubicalBoundary r := by
  obtain ⟨r, hr⟩ := qCube_three_boundary_reconstruction y hy hb
  have he := (qThreeCubicalBoundary_subdivision r).trans hr
  refine ⟨r, he, ?_⟩
  rw [← he, qSquare_coefficients_subdivision]

end FiniteChains.Davis
