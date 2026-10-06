module

public import RequestProject.QCubeSquareSubdivision
public import RequestProject.StrictLowerIntervalChains

@[expose] public section

/-! Actual strict subdivisions of quotient three-cubes. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

theorem threeFacet_uv_spx (c : QCube A) {u v w : V}
    (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) (s : ZMod 2) :
    (qCubeFacet c w s).spx = {u, v} := by
  ext x
  simp only [qCubeFacet, hs, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hne, hx | hx | hx⟩
    · exact Or.inl hx
    · exact Or.inr hx
    · exact False.elim (hne hx)
  · rintro (rfl | rfl)
    · exact ⟨huw, Or.inl rfl⟩
    · exact ⟨hvw, Or.inr (Or.inl rfl)⟩

theorem threeFacet_uw_spx (c : QCube A) {u v w : V}
    (huv : u ≠ v) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) (s : ZMod 2) :
    (qCubeFacet c v s).spx = {u, w} := by
  apply threeFacet_uv_spx c huv (Ne.symm hvw)
  rw [hs]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem threeFacet_vw_spx (c : QCube A) {u v w : V}
    (huv : u ≠ v) (huw : u ≠ w) (hs : c.spx = {u, v, w}) (s : ZMod 2) :
    (qCubeFacet c u s).spx = {v, w} := by
  apply threeFacet_uv_spx c (Ne.symm huv) (Ne.symm huw)
  rw [hs]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

noncomputable def cubeThreeSquareBoundary (c : QCube A) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) :
    (strictOrderCx (QCube A)).F →₀ ℤ :=
  cubeSquareSubdivision (qCubeFacet c w 0) u v huv (threeFacet_uv_spx c huw hvw hs 0) -
  cubeSquareSubdivision (qCubeFacet c w 1) u v huv (threeFacet_uv_spx c huw hvw hs 1) -
  cubeSquareSubdivision (qCubeFacet c v 0) u w huw (threeFacet_uw_spx c huv hvw hs 0) +
  cubeSquareSubdivision (qCubeFacet c v 1) u w huw (threeFacet_uw_spx c huv hvw hs 1) +
  cubeSquareSubdivision (qCubeFacet c u 0) v w hvw (threeFacet_vw_spx c huv huw hs 0) -
  cubeSquareSubdivision (qCubeFacet c u 1) v w hvw (threeFacet_vw_spx c huv huw hs 1)

theorem cubeThreeSquareBoundary_cycle (c : QCube A) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) :
    Comb.bdry2 (strictOrderCx (QCube A))
      (cubeThreeSquareBoundary c u v w huv huw hvw hs) = 0 := by
  simp only [cubeThreeSquareBoundary, map_sub, map_add, cubeSquareSubdivision_boundary,
    cubeSquareEdgeBoundary, oneCubeSubdivision]
  simp only [qCubeFacet_comm c (Ne.symm hvw) 0 0,
    qCubeFacet_comm c (Ne.symm hvw) 0 1, qCubeFacet_comm c (Ne.symm hvw) 1 0,
    qCubeFacet_comm c (Ne.symm hvw) 1 1,
    qCubeFacet_comm c (Ne.symm huw) 0 0, qCubeFacet_comm c (Ne.symm huw) 0 1,
    qCubeFacet_comm c (Ne.symm huw) 1 0, qCubeFacet_comm c (Ne.symm huw) 1 1,
    qCubeFacet_comm c (Ne.symm huv) 0 0, qCubeFacet_comm c (Ne.symm huv) 0 1,
    qCubeFacet_comm c (Ne.symm huv) 1 0, qCubeFacet_comm c (Ne.symm huv) 1 1]
  abel

/-- Every triangle in the cubical boundary lies strictly below its three-cube. -/
theorem cubeThreeSquareBoundary_support (c : QCube A) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w})
    (t : (strictOrderCx (QCube A)).F)
    (ht : t ∈ (cubeThreeSquareBoundary c u v w huv huw hvw hs).support) :
    t.1.2.2 < c := by
  classical
  by_contra hnot
  have hzero (d : QCube A) (hd : d < c) (a b : V) (hab : a ≠ b)
      (hspx : d.spx = {a, b}) : cubeSquareSubdivision d a b hab hspx t = 0 := by
    apply cubeSquareSubdivision_eq_zero_off_top
    intro he
    exact hnot (he.symm ▸ hd)
  have huf (s : ZMod 2) := qCubeFacet_lt c u s (by rw [hs]; simp)
  have hvf (s : ZMod 2) := qCubeFacet_lt c v s (by rw [hs]; simp)
  have hwf (s : ZMod 2) := qCubeFacet_lt c w s (by rw [hs]; simp)
  have he : cubeThreeSquareBoundary c u v w huv huw hvw hs t = 0 := by
    simp only [cubeThreeSquareBoundary, Finsupp.sub_apply, Finsupp.add_apply]
    rw [hzero _ (hwf 0), hzero _ (hwf 1), hzero _ (hvf 0), hzero _ (hvf 1),
      hzero _ (huf 0), hzero _ (huf 1)]
    norm_num
  exact (Finsupp.mem_support_iff.mp ht) he

/-- The six actual subdivided facets bound an actual strict tetrahedron chain. -/
theorem cubeThreeSquareBoundary_bounds (c : QCube A) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) :
    ∃ y : StrictOrdTet (QCube A) →₀ ℤ,
      strictOrdBoundary3 y = cubeThreeSquareBoundary c u v w huv huw hvw hs :=
  strictLowerCycle_bounds c _ (cubeThreeSquareBoundary_support c u v w huv huw hvw hs)
    (cubeThreeSquareBoundary_cycle c u v w huv huw hvw hs)

/-- A strict tetrahedral subdivision with the exact six-facet cubical boundary. -/
noncomputable def cubeThreeSubdivision (c : QCube A) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) :
    StrictOrdTet (QCube A) →₀ ℤ :=
  Classical.choose (cubeThreeSquareBoundary_bounds c u v w huv huw hvw hs)

theorem cubeThreeSubdivision_boundary (c : QCube A) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) :
    strictOrdBoundary3 (cubeThreeSubdivision c u v w huv huw hvw hs) =
      cubeThreeSquareBoundary c u v w huv huw hvw hs :=
  Classical.choose_spec (cubeThreeSquareBoundary_bounds c u v w huv huw hvw hs)

end FiniteChains.Davis
