module

public import RequestProject.CellularHomotopyChain
public import RequestProject.SurfaceCoverPolygonEquivariance
public import RequestProject.BarycentricTwoChains

@[expose] public section

/-! The boundary of the explicit subdivided polygon is its actual lifted
boundary path, with all sheets retained. Pending final Lean verification. -/
noncomputable section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.CoveredPolygon
open RACG Mirror Comb Cell
variable {κ ι P : Type} {M : ℕ} [NeZero M] [PartialOrder P]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)
  (f : P → SCell vc ec hc) (hf : IsPosetCover f)
  {v : PolygonCoverPole hc f} (D : CoveredPolygon hc f v)

def subdivisionBoundaryEdge (p : Fin M) :
    List ((orderCx (NeSpx (cmpRel P))).E × Bool) :=
  edgeHop (D.ve p) ++ revPath (edgeHop (D.v1e p))

theorem subdivisionBoundaryEdge_isPath (p : Fin M) :
    IsPath (orderCx (NeSpx (cmpRel P))).src (orderCx (NeSpx (cmpRel P))).tgt
      (D.subdivisionBoundaryEdge hc f p) (spx1 (D.V p)) (spx1 (D.V (p + 1))) :=
  (isPath_edgeHop (D.ve p)).append (isPath_revPath (isPath_edgeHop (D.v1e p)))

def subdivisionBoundaryPath : ℕ → List ((orderCx (NeSpx (cmpRel P))).E × Bool)
  | 0 => []
  | n + 1 => subdivisionBoundaryPath n ++ D.subdivisionBoundaryEdge hc f (cyc M n)

theorem subdivisionBoundaryPath_isPath (n : ℕ) :
    IsPath (orderCx (NeSpx (cmpRel P))).src (orderCx (NeSpx (cmpRel P))).tgt
      (D.subdivisionBoundaryPath hc f n) (spx1 (D.V (cyc M 0))) (spx1 (D.V (cyc M n))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := ih.append (D.subdivisionBoundaryEdge_isPath hc f (cyc M n))
    rw [← cyc_succ] at h
    exact h

theorem barycentricChain1_boundaryEdges :
    barycentricChain1 D.boundaryEdges =
      pathChain (D.subdivisionBoundaryPath hc f M) := by
  have hstep (p : Fin M) :
      pathChain (D.subdivisionBoundaryEdge hc f p) =
        barycentricChain1 (Finsupp.single ⟨(D.V p, D.E p), D.ve p⟩ 1 -
          Finsupp.single ⟨(D.V (p + 1), D.E p), D.v1e p⟩ 1) := by
    rw [subdivisionBoundaryEdge, pathChain_append, pathChain_revPath, map_sub]
    simp [edgeHop, hop, pathChain, ordPos, ordNeg, barycentricChain1,
      barycentricEdge, sub_eq_add_neg]
  have hpath (n : ℕ) : pathChain (D.subdivisionBoundaryPath hc f n) =
      ∑ k ∈ Finset.range n, pathChain (D.subdivisionBoundaryEdge hc f (cyc M k)) := by
    induction n with
    | zero => simp [subdivisionBoundaryPath, pathChain]
    | succ n ih => rw [subdivisionBoundaryPath, pathChain_append, ih, Finset.sum_range_succ]
  have hcyc (i : Fin M) : cyc M i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  rw [hpath]
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [hcyc]
  rw [boundaryEdges, map_sum]
  exact Finset.sum_congr rfl (fun p _ => (hstep p).symm)

theorem subdivisionBoundaryEdge_projection (p : Fin M) :
    mapPath (orderCxMap (barycentricMap f hf.mono) (barycentricMap_monotone f hf.mono))
      (D.subdivisionBoundaryEdge hc f p) = bdEdge hc p := by
  simp only [subdivisionBoundaryEdge, edgeHop, edgeHopRev, hop, bdEdge, revPath, revGerm,
    mapPath, List.map_append, List.map_cons, List.map_nil,
    List.reverse_cons, List.reverse_nil, List.nil_append]
  simp only [ordPos, ordNeg, Bool.not_false, Bool.not_true, orderCxMap,
    barycentricMap_spx1, barycentricMap_spx2, D.projV, D.projE]
  simp only [List.cons_append, List.nil_append]
  congr <;> exact Subsingleton.elim _ _

theorem subdivisionBoundaryPath_projection (n : ℕ) :
    mapPath (orderCxMap (barycentricMap f hf.mono) (barycentricMap_monotone f hf.mono))
      (D.subdivisionBoundaryPath hc f n) = bdPath hc n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [subdivisionBoundaryPath, mapPath_append, ih,
      D.subdivisionBoundaryEdge_projection hc f hf, bdPath]

theorem subdivisionFundamental_boundary :
    Comb.bdry2 (orderCx (NeSpx (cmpRel P))) (barycentricChain2 (decodeOrdNerve2 D.fundamental)) =
      pathChain (D.subdivisionBoundaryPath hc f M) := by
  rw [barycentricChain2_boundary, D.decodedFundamental_boundary,
    D.barycentricChain1_boundaryEdges hc f]

end FiniteChains.Davis.CoveredPolygon
