import RequestProject.SurfaceCells
import RequestProject.NerveDegree

/-! Explicit oriented chains of the polygon's triangulation, before identifying its sides. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open FreeAbelianGroup

def flagEdge {P : Type} (a b e : P) : Nerve.Ch P := of [a, e] - of [b, e]

def triangleFlagChain {P : Type} (a b c ab bc ca t : P) : Nerve.Ch P :=
  (of [a, ab, t] - of [b, ab, t]) +
  (of [b, bc, t] - of [c, bc, t]) +
  (of [c, ca, t] - of [a, ca, t])

theorem bdry_triangleFlagChain {P : Type} (a b c ab bc ca t : P) :
    Nerve.bdry (triangleFlagChain a b c ab bc ca t) =
      flagEdge a b ab + flagEdge b c bc + flagEdge c a ca := by
  simp only [triangleFlagChain, map_add, map_sub, Nerve.bdry_of,
    Nerve.bdryOn_cons, Nerve.bdryOn_nil, map_zero, sub_zero, Nerve.consMap_of]
  unfold flagEdge
  abel

theorem flagTriangle_mem_inc {P : Type} [Preorder P] {a e t : P}
    (hae : a ≤ e) (het : e ≤ t) : of [a, e, t] ∈ Nerve.Inc P :=
  Nerve.of_mem_inc (by simp [List.isChain_cons_cons, hae, het])

theorem triangleFlagChain_mem_inc {P : Type} [Preorder P] {a b c ab bc ca t : P}
    (ha : a ≤ ab) (hb : b ≤ ab) (hb' : b ≤ bc) (hc : c ≤ bc)
    (hc' : c ≤ ca) (ha' : a ≤ ca) (hab : ab ≤ t) (hbc : bc ≤ t) (hca : ca ≤ t) :
    triangleFlagChain a b c ab bc ca t ∈ Nerve.Inc P := by
  exact (Nerve.Inc P).add_mem
    ((Nerve.Inc P).add_mem
      ((Nerve.Inc P).sub_mem (flagTriangle_mem_inc ha hab) (flagTriangle_mem_inc hb hab))
      ((Nerve.Inc P).sub_mem (flagTriangle_mem_inc hb' hbc) (flagTriangle_mem_inc hc hbc)))
    ((Nerve.Inc P).sub_mem (flagTriangle_mem_inc hc' hca) (flagTriangle_mem_inc ha' hca))

variable {κ ι : Type} {M : ℕ} [NeZero M]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)

/-- The three oriented triangles in one polygon sector, each subdivided into six flags. -/
def polygonSectorChain (p : Fin M) : Nerve.Ch (SCell vc ec hc) :=
  triangleFlagChain (cV hc p) (cV hc (p + 1)) (cW hc (p + 1))
    (cE hc p) (cD hc (p + 1)) (cG hc p) (cT1 hc p) +
  triangleFlagChain (cV hc p) (cW hc (p + 1)) (cW hc p)
    (cG hc p) (cF hc p) (cD hc p) (cT2 hc p) +
  triangleFlagChain (cC hc) (cW hc p) (cW hc (p + 1))
    (cR hc p) (cF hc p) (cR hc (p + 1)) (cI hc p)

theorem polygonSectorChain_mem_inc (p : Fin M) :
    polygonSectorChain hc p ∈ Nerve.Inc (SCell vc ec hc) := by
  exact (Nerve.Inc _).add_mem ((Nerve.Inc _).add_mem
    (triangleFlagChain_mem_inc (cV_le_cE hc p) (cV1_le_cE hc p)
      (cV_le_cD hc (p + 1)) (cW_le_cD hc (p + 1))
      (cW1_le_cG hc p) (cV_le_cG hc p)
      (cE_le_cT1 hc p) (cD1_le_cT1 hc p) (cG_le_cT1 hc p))
    (triangleFlagChain_mem_inc (cV_le_cG hc p) (cW1_le_cG hc p)
      (cW1_le_cF hc p) (cW_le_cF hc p) (cW_le_cD hc p) (cV_le_cD hc p)
      (cG_le_cT2 hc p) (cF_le_cT2 hc p) (cD_le_cT2 hc p)))
    (triangleFlagChain_mem_inc (cC_le_cR hc p) (cW_le_cR hc p)
      (cW_le_cF hc p) (cW1_le_cF hc p)
      (cW_le_cR hc (p + 1)) (cC_le_cR hc (p + 1))
      (cR_le_cI hc p) (cF_le_cI hc p) (cR1_le_cI hc p))

/-- Internal diagonal and collar contributions cancel in each sector. -/
theorem bdry_polygonSectorChain (p : Fin M) :
    Nerve.bdry (polygonSectorChain hc p) =
      flagEdge (cV hc p) (cV hc (p + 1)) (cE hc p) +
      flagEdge (cV hc (p + 1)) (cW hc (p + 1)) (cD hc (p + 1)) -
      flagEdge (cV hc p) (cW hc p) (cD hc p) +
      flagEdge (cC hc) (cW hc p) (cR hc p) -
      flagEdge (cC hc) (cW hc (p + 1)) (cR hc (p + 1)) := by
  simp only [polygonSectorChain, map_add, bdry_triangleFlagChain, flagEdge]
  abel

/-- The complete polygon filling, with an explicit orientation on every flag triangle. -/
def polygonFundamentalChain : Nerve.Ch (SCell vc ec hc) :=
  ∑ p : Fin M, polygonSectorChain hc p

theorem polygonFundamentalChain_mem_inc :
    polygonFundamentalChain hc ∈ Nerve.Inc (SCell vc ec hc) :=
  (Nerve.Inc _).sum_mem (fun p _ => polygonSectorChain_mem_inc hc p)

/-- All internal edges cancel. Only the identified polygon boundary remains. -/
theorem bdry_polygonFundamentalChain :
    Nerve.bdry (polygonFundamentalChain hc) =
      ∑ p : Fin M, flagEdge (cV hc p) (cV hc (p + 1)) (cE hc p) := by
  have hshift (f : Fin M → Nerve.Ch (SCell vc ec hc)) :
      (∑ p : Fin M, f (p + 1)) = ∑ p : Fin M, f p :=
    Fintype.sum_equiv (Equiv.addRight (1 : Fin M)) _ _ (fun _ => rfl)
  simp only [polygonFundamentalChain, map_sum, bdry_polygonSectorChain,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hshift (fun p => flagEdge (cV hc p) (cW hc p) (cD hc p)),
    hshift (fun p => flagEdge (cC hc) (cW hc p) (cR hc p))]
  abel

theorem polygonFundamentalChain_degree :
    Nerve.lengthProjection 3 (polygonFundamentalChain hc) = polygonFundamentalChain hc := by
  simp [polygonFundamentalChain, polygonSectorChain, triangleFlagChain]

/-- Evaluate the coefficient of one specified inner flag; this detects the orientation. -/
noncomputable def innerFlagCoefficient : Nerve.Ch (SCell vc ec hc) →+ ℤ := by
  classical
  exact FreeAbelianGroup.lift (fun l => if l = [cC hc, cR hc 0, cI hc 0] then 1 else 0)

theorem innerFlagCoefficient_polygon (hM : 1 < M) :
    innerFlagCoefficient hc (polygonFundamentalChain hc) = 1 := by
  classical
  have h01 : (1 : Fin M) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt hM] at this
  have hr (p r : Fin M) : (Cell.rad p : SCell vc ec hc) = Cell.rad r ↔ p = r :=
    ⟨Cell.rad.inj, congrArg Cell.rad⟩
  have hi (p r : Fin M) : (Cell.inn p : SCell vc ec hc) = Cell.inn r ↔ p = r :=
    ⟨Cell.inn.inj, congrArg Cell.inn⟩
  have hsector (p : Fin M) :
      innerFlagCoefficient hc (polygonSectorChain hc p) = if p = 0 then 1 else 0 := by
    simp [innerFlagCoefficient, polygonSectorChain, triangleFlagChain,
      FreeAbelianGroup.lift_apply_of, cC, cR, cI, cV, cW, cE, cD, cG, cF, cT1, cT2, toS]
    by_cases hp : p = 0 <;> simp [hr, hi, hp, h01, List.cons.injEq]
  simp only [polygonFundamentalChain, map_sum, hsector]
  simp

theorem polygonFundamentalChain_ne_zero (hM : 1 < M) : polygonFundamentalChain hc ≠ 0 := by
  intro h
  have := innerFlagCoefficient_polygon hc hM
  rw [h, map_zero] at this
  exact zero_ne_one this

end FiniteChains.Davis
