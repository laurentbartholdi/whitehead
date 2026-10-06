module

public import RequestProject.QCubeEdgeChainEmbedding
public import RequestProject.QCubeSquareFrameUniqueness

@[expose] public section

/-! The actual cubical edge boundary and its faithful strict subdivision. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

noncomputable def qSquareSmallFacet (c : QSquare A) (s : ZMod 2) : QEdge A :=
  ⟨qCubeFacet c.1 (qSquareRight c) s, by
    rw [squareFacet_v_spx c.1 (qSquare_directions_ne c) (qSquare_free_directions c) s]
    simp⟩

noncomputable def qSquareLargeFacet (c : QSquare A) (s : ZMod 2) : QEdge A :=
  ⟨qCubeFacet c.1 (qSquareLeft c) s, by
    rw [squareFacet_w_spx c.1 (qSquare_directions_ne c) (qSquare_free_directions c) s]
    simp⟩

noncomputable def qSquareCubicalFaceBoundary (c : QSquare A) : QEdge A →₀ ℤ :=
  Finsupp.single (qSquareSmallFacet c 0) 1 - Finsupp.single (qSquareSmallFacet c 1) 1 -
    Finsupp.single (qSquareLargeFacet c 0) 1 + Finsupp.single (qSquareLargeFacet c 1) 1

noncomputable def qSquareCubicalBoundary : (QSquare A →₀ ℤ) →ₗ[ℤ] (QEdge A →₀ ℤ) :=
  Finsupp.linearCombination ℤ qSquareCubicalFaceBoundary

omit [LinearOrder V] in
theorem qEdgeChainSubdivision_single (c : QEdge A) (n : ℤ) :
    qEdgeChainSubdivision (Finsupp.single c n) = n • qEdgeSubdivision c := by
  rw [qEdgeChainSubdivision, Finsupp.linearCombination_single]

theorem qEdgeSubdivision_smallFacet (c : QSquare A) (s : ZMod 2) :
    qEdgeSubdivision (qSquareSmallFacet c s) =
      oneCubeSubdivision (qCubeFacet c.1 (qSquareRight c) s) (qSquareLeft c)
        (squareFacet_v_spx c.1 (qSquare_directions_ne c) (qSquare_free_directions c) s) :=
  qEdgeSubdivision_eq _ _ _

theorem qEdgeSubdivision_largeFacet (c : QSquare A) (s : ZMod 2) :
    qEdgeSubdivision (qSquareLargeFacet c s) =
      oneCubeSubdivision (qCubeFacet c.1 (qSquareLeft c) s) (qSquareRight c)
        (squareFacet_w_spx c.1 (qSquare_directions_ne c) (qSquare_free_directions c) s) :=
  qEdgeSubdivision_eq _ _ _

theorem qSquareCubicalFaceBoundary_subdivision (c : QSquare A) :
    qEdgeChainSubdivision (qSquareCubicalFaceBoundary c) =
      cubeSquareEdgeBoundary c.1 (qSquareLeft c) (qSquareRight c)
        (qSquare_directions_ne c) (qSquare_free_directions c) := by
  rw [qSquareCubicalFaceBoundary, map_add, map_sub, map_sub]
  simp only [qEdgeChainSubdivision_single, one_smul,
    qEdgeSubdivision_smallFacet, qEdgeSubdivision_largeFacet]
  rfl

/-- The actual cubical boundary commutes with the proved edge and square subdivisions. -/
theorem qSquareCubicalBoundary_subdivision (r : QSquare A →₀ ℤ) :
    qEdgeChainSubdivision (qSquareCubicalBoundary r) = qSquareFacetBoundary r := by
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s hr hs => rw [map_add, map_add, hr, hs, map_add]
  | single c n =>
      rw [qSquareCubicalBoundary, Finsupp.linearCombination_single, map_smul,
        qSquareCubicalFaceBoundary_subdivision, qSquareFacetBoundary,
        squareChainEdgeBoundary, Finsupp.linearCombination_single]

/-- Faithful edge subdivision reflects the actual cubical square-cycle equations. -/
theorem qSquareCubicalBoundary_zero_iff (r : QSquare A →₀ ℤ) :
    qSquareCubicalBoundary r = 0 ↔ qSquareFacetBoundary r = 0 := by
  constructor
  · intro h
    rw [← qSquareCubicalBoundary_subdivision, h, map_zero]
  · intro h
    apply qEdgeChainSubdivision_injective
    rwa [map_zero, qSquareCubicalBoundary_subdivision]

/-- Recovered coefficients of any actual two-dimensional strict cycle have zero actual
cubical edge boundary. -/
theorem qCube_twoCycle_cubical_coefficients_cycle
    (z : (strictOrderCx (QCube A)).F →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2.2.spx.card ≤ 2)
    (hcycle : Comb.bdry2 (strictOrderCx (QCube A)) z = 0) :
    qSquareCubicalBoundary (qSquareCycleCoefficients z) = 0 :=
  (qSquareCubicalBoundary_zero_iff _).mpr (qCube_twoCycle_coefficients_cycle z hz hcycle)

/-- Actual cubical square edge coefficients equal the coordinate incidences of the collapse. -/
theorem qSquareCubicalFaceBoundary_incidence [Fintype V] (c : QSquare A) :
    qSquareCubicalFaceBoundary c =
      incid (qCubeToCoordinate (qSquareSmallFacet c 0).1) (qSquareRight c) •
        Finsupp.single (qSquareSmallFacet c 0) 1 +
      incid (qCubeToCoordinate (qSquareSmallFacet c 1).1) (qSquareRight c) •
        Finsupp.single (qSquareSmallFacet c 1) 1 +
      incid (qCubeToCoordinate (qSquareLargeFacet c 0).1) (qSquareLeft c) •
        Finsupp.single (qSquareLargeFacet c 0) 1 +
      incid (qCubeToCoordinate (qSquareLargeFacet c 1).1) (qSquareLeft c) •
        Finsupp.single (qSquareLargeFacet c 1) 1 := by
  simp only [qSquareCubicalFaceBoundary, qSquareSmallFacet, qSquareLargeFacet]
  rw [squareFacet_incidence_small_zero c.1 (qSquare_directions_decreasing c)
      (qSquare_free_directions c),
    squareFacet_incidence_small_one c.1 (qSquare_directions_decreasing c)
      (qSquare_free_directions c),
    squareFacet_incidence_large_zero c.1 (qSquare_directions_decreasing c)
      (qSquare_free_directions c),
    squareFacet_incidence_large_one c.1 (qSquare_directions_decreasing c)
      (qSquare_free_directions c)]
  simp [sub_eq_add_neg]

end FiniteChains.Davis
