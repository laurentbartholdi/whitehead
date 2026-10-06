module

public import RequestProject.GenusSpineOriginAvoidance
public import RequestProject.QCubePositiveSquareCoefficients
public import RequestProject.GenusOldCubicalBoundaryRecovery

@[expose] public section

/-! Positive-square coefficients vanish in actual normalized old-spine cycles. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem markedSpineCycle_positive_square_zero (d : (markedSpineCx q).F →₀ ℤ)
    (hd : Comb.bdry2 (markedSpineCx q) d = 0)
    (s : QSquare (cmpRel (GenusVertex q))) (hs : s.1.sgn = 0) :
    qSquareCycleCoefficients (normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d)) s = 0 := by
  have hcycle : Comb.bdry2 (orderCx (QCube (cmpRel (GenusVertex q))))
      (chain2 (markedSpineToFullCube q) d) = 0 := by
    rw [bdry2_chain2, hd, map_zero]
  exact qSquareCycleCoefficients_positive_zero _
    (markedSpineToFullCube_normalized_dimension q d)
    (normalizeOrdChain2_cycle _ hcycle)
    (markedSpineToFullCube_normalized_zero_at_origin q d) s hs

/-- Every capped-cover cycle has an actual old-spine augmentation with zero positive
square coefficients and a genuine finite ordinary coordinate three-boundary. -/
theorem cappedCoverCycle_old_coordinate_boundary_positive_zero
    (c : (cappedTreeCover q).F →₀ ℤ) (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ (d : (markedSpineCx q).F →₀ ℤ)
      (r : QThreeCube (cmpRel (GenusVertex q)) →₀ ℤ),
      Finsupp.mapDomain Sum.inl d = Finsupp.mapDomain Prod.snd c ∧
      Comb.bdry2 (markedSpineCx q) d = 0 ∧
      (∀ s : QSquare (cmpRel (GenusVertex q)), s.1.sgn = 0 →
        qSquareCycleCoefficients (normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d)) s = 0) ∧
      Finsupp.lmapDomain ℤ ℤ (fun s : QSquare (cmpRel (GenusVertex q)) => qCubeToCoordinate s.1)
        (qSquareCycleCoefficients (normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d))) =
      Finsupp.linearCombination ℤ
        (fun t : QThreeCube (cmpRel (GenusVertex q)) => qCubeCoordinateFacetChain t.1) r := by
  obtain ⟨d, r, hd, hcycle, hr⟩ := cappedCoverCycle_old_coordinate_boundary q c hc
  exact ⟨d, r, hd, hcycle, markedSpineCycle_positive_square_zero q d hcycle, hr⟩

end FiniteChains.Davis.Genus
