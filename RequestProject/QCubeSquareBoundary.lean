import RequestProject.QCubeFacets

/-! The actual oriented edge cycle of a two-dimensional quotient cube. -/
open scoped Classical

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

theorem squareFacet_v_spx (c : QCube A) {v w : V} (hne : v ≠ w)
    (hs : c.spx = {v, w}) (s : ZMod 2) : (qCubeFacet c w s).spx = {v} := by
  ext x
  simp only [qCubeFacet, hs, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hxv | hxw⟩
    · exact hxv
    · exact False.elim (hx hxw)
  · rintro rfl
    exact ⟨hne, Or.inl rfl⟩

theorem squareFacet_w_spx (c : QCube A) {v w : V} (hne : v ≠ w)
    (hs : c.spx = {v, w}) (s : ZMod 2) : (qCubeFacet c v s).spx = {w} := by
  simp [qCubeFacet, hs, hne]

/-- The oriented cubical boundary in the direction frame `(v, w)`.
For `w < v`, this agrees with the coordinate incidence convention in `MomentAngle`. -/
noncomputable def cubeSquareEdgeBoundary (c : QCube A) (v w : V) (hne : v ≠ w)
    (hs : c.spx = {v, w}) : (strictOrderCx (QCube A)).E →₀ ℤ :=
  oneCubeSubdivision (qCubeFacet c w 0) v (squareFacet_v_spx c hne hs 0) -
  oneCubeSubdivision (qCubeFacet c w 1) v (squareFacet_v_spx c hne hs 1) -
  oneCubeSubdivision (qCubeFacet c v 0) w (squareFacet_w_spx c hne hs 0) +
  oneCubeSubdivision (qCubeFacet c v 1) w (squareFacet_w_spx c hne hs 1)

/-- Every actual oriented subdivided square boundary is a strict cellular edge cycle. -/
theorem cubeSquareEdgeBoundary_cycle (c : QCube A) (v w : V) (hne : v ≠ w)
    (hs : c.spx = {v, w}) :
    Comb.bdry1 (strictOrderCx (QCube A)) (cubeSquareEdgeBoundary c v w hne hs) = 0 := by
  rw [cubeSquareEdgeBoundary, map_add, map_sub, map_sub,
    oneCubeSubdivision_facet_boundary, oneCubeSubdivision_facet_boundary,
    oneCubeSubdivision_facet_boundary, oneCubeSubdivision_facet_boundary]
  rw [qCubeFacet_comm c (Ne.symm hne) 0 0, qCubeFacet_comm c (Ne.symm hne) 0 1,
    qCubeFacet_comm c (Ne.symm hne) 1 0, qCubeFacet_comm c (Ne.symm hne) 1 1]
  abel

/-- Restriction to one facet recovers its nonzero oriented edge subdivision. -/
theorem cubeSquareEdgeBoundary_filter_facet (c : QCube A) (v w : V) (hne : v ≠ w)
    (hs : c.spx = {v, w}) :
    (cubeSquareEdgeBoundary c v w hne hs).filter
      (fun e : (strictOrderCx (QCube A)).E => e.1.2 = qCubeFacet c w 0) =
      oneCubeSubdivision (qCubeFacet c w 0) v (squareFacet_v_spx c hne hs 0) := by
  classical
  have hw : qCubeFacet c w 1 ≠ qCubeFacet c w 0 := by
    intro h
    have he := congrArg (fun d : QCube A => d.sgn w) h
    simp only [qCubeFacet_sgn_self] at he
    norm_num at he
  have hcross (s t : ZMod 2) : qCubeFacet c v s ≠ qCubeFacet c w t := by
    intro h
    have he := congrArg QCube.spx h
    rw [squareFacet_w_spx c hne hs s, squareFacet_v_spx c hne hs t] at he
    exact hne (Finset.singleton_inj.mp he).symm
  simp [cubeSquareEdgeBoundary, oneCubeSubdivision, cubeEdgeSubdivision_filter_tgt,
    hw, hcross 0 0, hcross 1 0]

theorem cubeSquareEdgeBoundary_ne_zero (c : QCube A) (v w : V) (hne : v ≠ w)
    (hs : c.spx = {v, w}) : cubeSquareEdgeBoundary c v w hne hs ≠ 0 := by
  classical
  intro h
  have he := congrArg (Finsupp.filter
    (fun e : (strictOrderCx (QCube A)).E => e.1.2 = qCubeFacet c w 0)) h
  rw [cubeSquareEdgeBoundary_filter_facet, Finsupp.filter_zero] at he
  exact cubeEdgeSubdivision_ne_zero (qCubeFacet c w 0) v _ he

end FiniteChains.Davis
