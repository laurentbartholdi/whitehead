import RequestProject.QCubeThreeFaceEdges
import RequestProject.CubicalThreeBoundaryMatrix

/-! The indexed six-face boundary is the actual geometric cubical boundary. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qThreeFace_boundary_column (c : QCube A) (u v w : V)
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) (i : Fin 3 × ZMod 2) :
    qSquareCubicalFaceBoundary
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs i) =
      Finsupp.lmapDomain ℤ ℤ
        (qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
          (Ne.symm hvw.ne) hs) (threeFacetBoundaryColumn i) := by
  classical
  obtain ⟨e, s⟩ := i
  fin_cases e
  · change qSquareCubicalFaceBoundary
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (0, s)) =
      Finsupp.lmapDomain ℤ ℤ
        (qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
          (Ne.symm hvw.ne) hs) (threeFacetBoundaryColumn (0, s))
    simp only [threeFacetBoundaryColumn, Fin.isValue, reduceIte]
    simp only [map_add, map_sub, map_neg, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single, qSquareCubicalFaceBoundary]
    rw [qThreeFaceSquare_zero_small c u v w huv hvw hs s 0,
      qThreeFaceSquare_zero_small c u v w huv hvw hs s 1,
      qThreeFaceSquare_zero_large c u v w huv hvw hs s 0,
      qThreeFaceSquare_zero_large c u v w huv hvw hs s 1]
    abel
  · change qSquareCubicalFaceBoundary
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (1, s)) =
      Finsupp.lmapDomain ℤ ℤ
        (qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
          (Ne.symm hvw.ne) hs) (threeFacetBoundaryColumn (1, s))
    simp only [threeFacetBoundaryColumn, Fin.isValue,
      show (1 : Fin 3) ≠ 0 by decide, reduceIte]
    simp only [map_add, map_sub, map_neg, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single, qSquareCubicalFaceBoundary]
    rw [qThreeFaceSquare_one_small c u v w huv hvw hs s 0,
      qThreeFaceSquare_one_small c u v w huv hvw hs s 1,
      qThreeFaceSquare_one_large c u v w huv hvw hs s 0,
      qThreeFaceSquare_one_large c u v w huv hvw hs s 1]
    abel
  · change qSquareCubicalFaceBoundary
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (2, s)) =
      Finsupp.lmapDomain ℤ ℤ
        (qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
          (Ne.symm hvw.ne) hs) (threeFacetBoundaryColumn (2, s))
    simp only [threeFacetBoundaryColumn, Fin.isValue,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, reduceIte]
    simp only [map_add, map_sub, map_neg, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single, qSquareCubicalFaceBoundary]
    rw [qThreeFaceSquare_two_small c u v w huv hvw hs s 0,
      qThreeFaceSquare_two_small c u v w huv hvw hs s 1,
      qThreeFaceSquare_two_large c u v w huv hvw hs s 0,
      qThreeFaceSquare_two_large c u v w huv hvw hs s 1]
    abel

/-- Boundary naturality for every finite chain of actual indexed square facets. -/
theorem qThreeFace_boundary_naturality (c : QCube A) (u v w : V)
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w})
    (r : (Fin 3 × ZMod 2) →₀ ℤ) :
    qSquareCubicalBoundary
      (Finsupp.lmapDomain ℤ ℤ
        (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
          (Ne.symm hvw.ne) hs) r) =
      Finsupp.lmapDomain ℤ ℤ
        (qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
          (Ne.symm hvw.ne) hs) (threeFacetBoundaryMatrix r) := by
  classical
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r z hr hz => simp only [map_add, hr, hz]
  | single i n =>
      rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
        qSquareCubicalBoundary, Finsupp.linearCombination_single,
        threeFacetBoundaryMatrix, Finsupp.linearCombination_single, map_smul,
        qThreeFace_boundary_column c u v w huv hvw hs i]

end FiniteChains.Davis
