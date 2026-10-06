module

public import RequestProject.QCubeThreeSubdivision
public import RequestProject.MomentAngle

@[expose] public section

/-! Actual quotient facets have the cubical collapse's coordinate incidence signs. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [Fintype V] [LinearOrder V] {A : CommRel V}

theorem qCubeFacet_incidence_zero (c : QCube A) (v : V) :
    incid (qCubeToCoordinate (qCubeFacet c v 0)) v =
      (-1 : ℤ) ^ ((c.spx.erase v).filter (fun i => i < v)).card := by
  simp [incid, freeSet_qCubeToCoordinate, qCubeToCoordinate, qCubeFacet, CubeCoord.sgn]

theorem qCubeFacet_incidence_one (c : QCube A) (v : V) :
    incid (qCubeToCoordinate (qCubeFacet c v 1)) v =
      -((-1 : ℤ) ^ ((c.spx.erase v).filter (fun i => i < v)).card) := by
  simp [incid, freeSet_qCubeToCoordinate, qCubeToCoordinate, qCubeFacet, CubeCoord.sgn]

/-- In the decreasing direction frame, the smaller-direction positive facet has sign +1. -/
theorem squareFacet_incidence_small_zero (c : QCube A) {v w : V}
    (h : w < v) (hs : c.spx = {v, w}) :
    incid (qCubeToCoordinate (qCubeFacet c w 0)) w = 1 := by
  rw [qCubeFacet_incidence_zero]
  have he : (c.spx.erase w).filter (fun i => i < w) = ∅ := by
    rw [hs]
    ext i
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hiw, rfl | rfl⟩, hi⟩
    · exact (not_lt_of_ge h.le) hi
    · exact hiw rfl
  rw [he]
  norm_num

/-- In the decreasing direction frame, the larger-direction positive facet has sign -1. -/
theorem squareFacet_incidence_large_zero (c : QCube A) {v w : V}
    (h : w < v) (hs : c.spx = {v, w}) :
    incid (qCubeToCoordinate (qCubeFacet c v 0)) v = -1 := by
  rw [qCubeFacet_incidence_zero]
  have he : (c.spx.erase v).filter (fun i => i < v) = {w} := by
    rw [hs]
    ext i
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hi, rfl | rfl⟩, _⟩
      · exact False.elim (hi rfl)
      · rfl
    · rintro rfl
      exact ⟨⟨h.ne, Or.inr rfl⟩, h⟩
  rw [he]
  norm_num

theorem squareFacet_incidence_small_one (c : QCube A) {v w : V}
    (h : w < v) (hs : c.spx = {v, w}) :
    incid (qCubeToCoordinate (qCubeFacet c w 1)) w = -1 := by
  rw [qCubeFacet_incidence_one]
  have he := squareFacet_incidence_small_zero c h hs
  rw [qCubeFacet_incidence_zero] at he
  rw [he]

theorem squareFacet_incidence_large_one (c : QCube A) {v w : V}
    (h : w < v) (hs : c.spx = {v, w}) :
    incid (qCubeToCoordinate (qCubeFacet c v 1)) v = 1 := by
  rw [qCubeFacet_incidence_one]
  have he := squareFacet_incidence_large_zero c h hs
  rw [qCubeFacet_incidence_zero] at he
  rw [he]
  norm_num

/-- The six signs of an actual three-cube in decreasing coordinate order. -/
theorem threeFacet_incidence_zero (c : QCube A) {u v w : V}
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) :
    incid (qCubeToCoordinate (qCubeFacet c w 0)) w = 1 ∧
    incid (qCubeToCoordinate (qCubeFacet c v 0)) v = -1 ∧
    incid (qCubeToCoordinate (qCubeFacet c u 0)) u = 1 := by
  have huw := hvw.trans huv
  have he : ({v, w} : Finset V).erase u = {v, w} :=
    Finset.erase_eq_of_notMem (by simp [Ne.symm huv.ne, Ne.symm huw.ne])
  simp [qCubeFacet_incidence_zero, hs, Finset.filter_erase, Finset.filter_insert, Finset.filter_singleton,
    huv, hvw, huw, not_lt_of_ge huv.le, not_lt_of_ge hvw.le, not_lt_of_ge huw.le,
    he, Ne.symm hvw.ne]

theorem threeFacet_incidence_one (c : QCube A) {u v w : V}
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) :
    incid (qCubeToCoordinate (qCubeFacet c w 1)) w = -1 ∧
    incid (qCubeToCoordinate (qCubeFacet c v 1)) v = 1 ∧
    incid (qCubeToCoordinate (qCubeFacet c u 1)) u = -1 := by
  obtain ⟨hw, hv, hu⟩ := threeFacet_incidence_zero c huv hvw hs
  simp only [qCubeFacet_incidence_zero] at hw hv hu
  simp only [qCubeFacet_incidence_one, hw, hv, hu]
  norm_num

/-- The subdivided square boundary is precisely the sum weighted by coordinate incidences. -/
theorem cubeSquareEdgeBoundary_incidence (c : QCube A) {v w : V}
    (h : w < v) (hs : c.spx = {v, w}) :
    cubeSquareEdgeBoundary c v w (Ne.symm h.ne) hs =
      incid (qCubeToCoordinate (qCubeFacet c w 0)) w •
        oneCubeSubdivision (qCubeFacet c w 0) v (squareFacet_v_spx c (Ne.symm h.ne) hs 0) +
      incid (qCubeToCoordinate (qCubeFacet c w 1)) w •
        oneCubeSubdivision (qCubeFacet c w 1) v (squareFacet_v_spx c (Ne.symm h.ne) hs 1) +
      incid (qCubeToCoordinate (qCubeFacet c v 0)) v •
        oneCubeSubdivision (qCubeFacet c v 0) w (squareFacet_w_spx c (Ne.symm h.ne) hs 0) +
      incid (qCubeToCoordinate (qCubeFacet c v 1)) v •
        oneCubeSubdivision (qCubeFacet c v 1) w (squareFacet_w_spx c (Ne.symm h.ne) hs 1) := by
  rw [squareFacet_incidence_small_zero c h hs, squareFacet_incidence_small_one c h hs,
    squareFacet_incidence_large_zero c h hs, squareFacet_incidence_large_one c h hs]
  simp [cubeSquareEdgeBoundary, sub_eq_add_neg]

/-- The six subdivided square facets carry exactly the coordinate incidence coefficients. -/
theorem cubeThreeSquareBoundary_incidence (c : QCube A) {u v w : V}
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) :
    cubeThreeSquareBoundary c u v w (Ne.symm huv.ne)
      (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs =
      incid (qCubeToCoordinate (qCubeFacet c w 0)) w •
        cubeSquareSubdivision (qCubeFacet c w 0) u v (Ne.symm huv.ne) (threeFacet_uv_spx c (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs 0) +
      incid (qCubeToCoordinate (qCubeFacet c w 1)) w •
        cubeSquareSubdivision (qCubeFacet c w 1) u v (Ne.symm huv.ne) (threeFacet_uv_spx c (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs 1) +
      incid (qCubeToCoordinate (qCubeFacet c v 0)) v •
        cubeSquareSubdivision (qCubeFacet c v 0) u w (Ne.symm (hvw.trans huv).ne) (threeFacet_uw_spx c (Ne.symm huv.ne) (Ne.symm hvw.ne) hs 0) +
      incid (qCubeToCoordinate (qCubeFacet c v 1)) v •
        cubeSquareSubdivision (qCubeFacet c v 1) u w (Ne.symm (hvw.trans huv).ne) (threeFacet_uw_spx c (Ne.symm huv.ne) (Ne.symm hvw.ne) hs 1) +
      incid (qCubeToCoordinate (qCubeFacet c u 0)) u •
        cubeSquareSubdivision (qCubeFacet c u 0) v w (Ne.symm hvw.ne) (threeFacet_vw_spx c (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne) hs 0) +
      incid (qCubeToCoordinate (qCubeFacet c u 1)) u •
        cubeSquareSubdivision (qCubeFacet c u 1) v w (Ne.symm hvw.ne) (threeFacet_vw_spx c (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne) hs 1) := by
  obtain ⟨hw0, hv0, hu0⟩ := threeFacet_incidence_zero c huv hvw hs
  obtain ⟨hw1, hv1, hu1⟩ := threeFacet_incidence_one c huv hvw hs
  rw [hw0, hw1, hv0, hv1, hu0, hu1]
  simp [cubeThreeSquareBoundary, sub_eq_add_neg]

end FiniteChains.Davis
