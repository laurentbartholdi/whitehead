module

public import RequestProject.QCubeThreeOrderedCoordinates
public import RequestProject.CubicalThreeOrientationChain

@[expose] public section

/-! The indexed oriented six-face chain subdivides to the actual three-cube boundary. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qThreeOrientedFaces_subdivision (c : QCube A) (u v w : V)
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) :
    qSquareChainSubdivision
      (Finsupp.lmapDomain ℤ ℤ
        (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
          (Ne.symm hvw.ne) hs) threeOrientedFaces) =
      cubeThreeSquareBoundary c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs := by
  classical
  let f := qThreeFaceSquare c u v w (Ne.symm huv.ne)
    (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs
  have h0 (s : ZMod 2) : qSquareChainSubdivision (Finsupp.single (f (0, s)) 1) =
      cubeSquareSubdivision (qCubeFacet c u s) v w (Ne.symm hvw.ne)
        (threeFacet_vw_spx c (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne) hs s) := by
    rw [qSquare_subdivision_single _ 1 hvw
      (threeFacet_vw_spx c (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne) hs s)]
    simp only [one_smul]
    rfl
  have h1 (s : ZMod 2) : qSquareChainSubdivision (Finsupp.single (f (1, s)) 1) =
      cubeSquareSubdivision (qCubeFacet c v s) u w (Ne.symm (hvw.trans huv).ne)
        (threeFacet_uw_spx c (Ne.symm huv.ne) (Ne.symm hvw.ne) hs s) := by
    rw [qSquare_subdivision_single _ 1 (hvw.trans huv)
      (threeFacet_uw_spx c (Ne.symm huv.ne) (Ne.symm hvw.ne) hs s)]
    simp only [one_smul]
    rfl
  have h2 (s : ZMod 2) : qSquareChainSubdivision (Finsupp.single (f (2, s)) 1) =
      cubeSquareSubdivision (qCubeFacet c w s) u v (Ne.symm huv.ne)
        (threeFacet_uv_spx c (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs s) := by
    rw [qSquare_subdivision_single _ 1 huv
      (threeFacet_uv_spx c (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs s)]
    simp only [one_smul]
    rfl
  change qSquareChainSubdivision (Finsupp.lmapDomain ℤ ℤ f threeOrientedFaces) = _
  simp only [threeOrientedFaces, map_sub, map_add,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [h0, h0, h1, h1, h2, h2]
  unfold cubeThreeSquareBoundary
  abel

/-- Every actual square cycle supported on a three-cube's facets subdivides to a scalar
multiple of its actual oriented cubical boundary. -/
theorem qThreeFacetCycle_subdivision (c : QCube A) (u v w : V)
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w})
    (r : QSquare A →₀ ℤ) (hr : ∀ s ∈ r.support, s.1 < c)
    (hcycle : qSquareCubicalBoundary r = 0) :
    ∃ k : ℤ, qSquareChainSubdivision r = k •
      cubeThreeSquareBoundary c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs := by
  classical
  let f := qThreeFaceSquare c u v w (Ne.symm huv.ne)
    (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs
  let z := qThreeOrderedCoordinates c u v w (Ne.symm huv.ne)
    (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs r
  have hrecon : Finsupp.lmapDomain ℤ ℤ f z = r :=
    qThreeOrderedCoordinates_reconstruct c u v w (Ne.symm huv.ne)
      (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs r hr
  have hz : qSquareCubicalBoundary (Finsupp.lmapDomain ℤ ℤ f z) = 0 := by
    rwa [hrecon]
  have hcoeff := qThreeFace_cycle_coefficients c u v w huv hvw hs z hz
  have he : z = z (0, 0) • threeOrientedFaces := by
    ext i
    rw [Finsupp.smul_apply, threeOrientedFaces_apply, hcoeff i]
    rfl
  refine ⟨z (0, 0), ?_⟩
  conv_lhs => rw [← hrecon, he, map_smul, map_smul]
  exact congrArg (fun x => z (0, 0) • x) (qThreeOrientedFaces_subdivision c u v w huv hvw hs)

end FiniteChains.Davis
