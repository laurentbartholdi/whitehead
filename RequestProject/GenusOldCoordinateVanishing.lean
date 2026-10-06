import RequestProject.GenusSpineCoordinateSupport

/-! Actual old-spine square coefficients vanish after the capped-cover augmentation. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem markedSpineSquareCoefficients_zero_of_collapse (d : (markedSpineCx q).F →₀ ℤ)
    (hd : CollapseChain.cmap (cubeBdry (V := GenusVertex q)) (genusChainCollapse q)
      (markedSpineExtendedCoordinateChain q d) = 0) :
    markedSpineSquareCoefficients q d = 0 := by
  classical
  have hfun : (markedSpineExtendedCoordinateChain q d :
      (Cube (GenusVertex q) ⊕ Finset (GenusVertex q)) → ℤ) = 0 := by
    rw [← markedSpineExtendedCoordinateChain_fixed q d]
    exact hd
  have hfin : markedSpineExtendedCoordinateChain q d = 0 := by
    ext f
    exact congrFun hfun f
  have hcoord : markedSpineCoordinateChain q d = 0 := by
    apply Finsupp.mapDomain_injective
      (Sum.inl_injective : Function.Injective
        (Sum.inl : Cube (GenusVertex q) → Cube (GenusVertex q) ⊕ Finset (GenusVertex q)))
    change markedSpineExtendedCoordinateChain q d = Finsupp.mapDomain _ 0
    rw [Finsupp.mapDomain_zero]
    exact hfin
  apply Finsupp.mapDomain_injective
    (show Function.Injective
      (fun s : QSquare (cmpRel (GenusVertex q)) => qCubeToCoordinate s.1) from
      fun _ _ h => Subtype.ext (qCubeToCoordinate_injective h))
  change markedSpineCoordinateChain q d = Finsupp.mapDomain _ 0
  rw [Finsupp.mapDomain_zero]
  exact hcoord

/-- For an actual old-spine cycle, zero recovered square coefficients imply its normalized
full-cube image is the zero chain by the proved two-cycle subdivision dictionary. -/
theorem markedSpine_normalized_image_zero_of_coefficients (d : (markedSpineCx q).F →₀ ℤ)
    (hd : Comb.bdry2 (markedSpineCx q) d = 0)
    (hcoeff : markedSpineSquareCoefficients q d = 0) :
    normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d) = 0 := by
  have hcycle : Comb.bdry2 (orderCx (QCube (cmpRel (GenusVertex q))))
      (chain2 (markedSpineToFullCube q) d) = 0 := by
    rw [bdry2_chain2, hd, map_zero]
  have he := qCube_twoCycle_reconstruction _
    (markedSpineToFullCube_normalized_dimension q d) (normalizeOrdChain2_cycle _ hcycle)
  change qSquareChainSubdivision (markedSpineSquareCoefficients q d) = _ at he
  rw [hcoeff, map_zero] at he
  exact he.symm

/-- Every actual capped-cover cycle augments into an old-spine cycle whose normalized
full-cube chain image is exactly zero. -/
theorem cappedCoverCycle_old_normalized_image_zero
    (c : (cappedTreeCover q).F →₀ ℤ) (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ d : (markedSpineCx q).F →₀ ℤ,
      Finsupp.mapDomain Sum.inl d = Finsupp.mapDomain Prod.snd c ∧
      Comb.bdry2 (markedSpineCx q) d = 0 ∧
      normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d) = 0 := by
  obtain ⟨d, hd, hcycle, hcollapse⟩ := cappedCoverCycle_oldCoordinate_collapse_zero q c hc
  exact ⟨d, hd, hcycle, markedSpine_normalized_image_zero_of_coefficients q d hcycle
    (markedSpineSquareCoefficients_zero_of_collapse q d hcollapse)⟩

end FiniteChains.Davis.Genus
