module

public import RequestProject.GenusSpineFullCubeDimension
public import RequestProject.GenusOldAugmentationReduction

@[expose] public section

/-! Actual capped-cover cycles recover finite ordinary cubical boundaries on old spine images. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

/-- The actual old spine image of every capped-cover cycle, after ordinary normalization
and square coefficient recovery, is a genuine finite coordinate three-boundary. -/
theorem cappedCoverCycle_old_coordinate_boundary (c : (cappedTreeCover q).F →₀ ℤ)
    (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ (d : (markedSpineCx q).F →₀ ℤ)
      (r : QThreeCube (cmpRel (GenusVertex q)) →₀ ℤ),
      Finsupp.mapDomain Sum.inl d = Finsupp.mapDomain Prod.snd c ∧
      Comb.bdry2 (markedSpineCx q) d = 0 ∧
      Finsupp.lmapDomain ℤ ℤ (fun s : QSquare (cmpRel (GenusVertex q)) => qCubeToCoordinate s.1)
        (qSquareCycleCoefficients (normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d))) =
      Finsupp.linearCombination ℤ
        (fun t : QThreeCube (cmpRel (GenusVertex q)) => qCubeCoordinateFacetChain t.1) r := by
  obtain ⟨d, hd, hcycle, y, hy⟩ := cappedCoverCycle_old_augmentation_cycle q c hc
  obtain ⟨z, hz⟩ := normalized_boundary3 _ ⟨y, hy⟩
  have hdim : ∀ t ∈ z.support, t.1.2.2.2.spx.card ≤ 3 := by
    intro t _
    exact genus_chain_card_le_three q (genus_simplex_mem_faces q t.1.2.2.2.isSimplex)
  have hb : ∀ s ∈ (strictOrdBoundary3 z).support, s.1.2.2.spx.card ≤ 2 := by
    intro s hs
    rw [hz] at hs
    exact markedSpineToFullCube_normalized_dimension q d s hs
  obtain ⟨r, hr⟩ := qCube_three_coordinate_boundary_reconstruction z hdim hb
  refine ⟨d, r, hd, hcycle, ?_⟩
  rwa [hz] at hr

end FiniteChains.Davis.Genus
