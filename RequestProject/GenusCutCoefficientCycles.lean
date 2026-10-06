module

public import RequestProject.GenusPositiveSquareCoefficients
public import RequestProject.QCubePositiveCoordinateChains

@[expose] public section

/-! Actual recovered cut-face coefficients are cycles killed by the genus collapse. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem genus_cutFaceChain_cycle_of_old_boundary (d : (markedSpineCx q).F →₀ ℤ)
    (hd : Comb.bdry2 (markedSpineCx q) d = 0)
    (r : QThreeCube (cmpRel (GenusVertex q)) →₀ ℤ)
    (he : Finsupp.lmapDomain ℤ ℤ
      (fun s : QSquare (cmpRel (GenusVertex q)) => qCubeToCoordinate s.1)
      (qSquareCycleCoefficients (normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d))) =
      Finsupp.linearCombination ℤ
        (fun t : QThreeCube (cmpRel (GenusVertex q)) => qCubeCoordinateFacetChain t.1) r) :
    simpBdry (qThreeCutFaceChain r) = 0 := by
  apply qThreeCutFaceChain_cycle
  intro σ
  rw [← he]
  exact qSquareCoordinate_positive_zero _ (markedSpineCycle_positive_square_zero q d hd) σ

/-- The cut correction of an actual ordinary boundary of an old-spine cycle is killed
by the already constructed geometric genus collapse. -/
theorem genus_cutFaceChain_collapse_zero_of_old_boundary (d : (markedSpineCx q).F →₀ ℤ)
    (hd : Comb.bdry2 (markedSpineCx q) d = 0)
    (r : QThreeCube (cmpRel (GenusVertex q)) →₀ ℤ)
    (he : Finsupp.lmapDomain ℤ ℤ
      (fun s : QSquare (cmpRel (GenusVertex q)) => qCubeToCoordinate s.1)
      (qSquareCycleCoefficients (normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d))) =
      Finsupp.linearCombination ℤ
        (fun t : QThreeCube (cmpRel (GenusVertex q)) => qCubeCoordinateFacetChain t.1) r) :
    CollapseChain.cmap (cubeBdry (V := GenusVertex q)) (genusChainCollapse q)
      (Sum.elim 0 (fun σ => -qThreeCutFaceChain r σ)) = 0 := by
  apply genusChainCollapse_cutSurface_eq_zero q (qThreeCutFaceChain r)
    (genus_cutFaceChain_cycle_of_old_boundary q d hd r he)
  · intro σ hnot
    by_contra hn
    exact hnot (qThreeCutFaceChain_support r σ hn).1
  · intro σ hnot
    by_contra hn
    exact hnot (genus_simplex_mem_faces q (qThreeCutFaceChain_support r σ hn).2)

end FiniteChains.Davis.Genus
