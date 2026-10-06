module

public import RequestProject.GenusSpineCycleFaithfulness
public import RequestProject.GenusOldCoordinateVanishing

@[expose] public section

/-! Actual old-spine and total capped-cover augmentation vanishing, with all dependencies proved. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

/-- The actual normalized full-cube comparison reflects zero on marked-spine cycles,
by the retained-cell retraction and faithful ordinary triangle coordinates. -/
theorem markedSpine_cycle_zero_of_normalized_full_image (d : (markedSpineCx q).F →₀ ℤ)
    (hd : Comb.bdry2 (markedSpineCx q) d = 0)
    (hz : normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d) = 0) : d = 0 := by
  change Comb.bdry2 (component (genusSpineCx q) (spineBase q)) d = 0 at hd
  let c := chain2 (componentIncl (genusSpineCx q) (spineBase q)) d
  have hcycle : Comb.bdry2 (genusSpineCx q) c = 0 := by
    rw (config := { transparency := .default }) [bdry2_chain2, hd, map_zero]
  have he : normalizedStrictChain2 (genusSpineCellToFullCube q)
      (genusSpineCellToFullCube_monotone q) c =
      normalizeOrdChain2 (chain2 (markedSpineToFullCube q) d) := by
    change normalizeOrdChain2 (Finsupp.mapDomain
        (orderCxMap (genusSpineCellToFullCube q) (genusSpineCellToFullCube_monotone q)).onF
        (Finsupp.mapDomain (strictOrderIncl (GenusSpineCell q)).onF
          (Finsupp.mapDomain (componentIncl (genusSpineCx q) (spineBase q)).onF d))) =
      normalizeOrdChain2 (Finsupp.mapDomain (markedSpineToFullCube q).onF d)
    rw (config := { transparency := .default }) [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    rfl
  have hc := genusSpine_cycle_zero_of_normalized_full_image q c hcycle (he.trans hz)
  apply Finsupp.mapDomain_injective
    (componentIncl_injective_onF (X := genusSpineCx q) (spineBase q))
  change c = Finsupp.mapDomain _ 0
  rw (config := { transparency := .default }) [Finsupp.mapDomain_zero]
  exact hc

/-- Every actual capped-cover cycle has zero old-spine augmentation. -/
theorem cappedCoverCycle_old_augmentation_zero
    (c : (cappedTreeCover q).F →₀ ℤ) (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ d : (markedSpineCx q).F →₀ ℤ,
      Finsupp.mapDomain Sum.inl d = Finsupp.mapDomain Prod.snd c ∧ d = 0 := by
  obtain ⟨d, hd, hcycle, hz⟩ := cappedCoverCycle_old_normalized_image_zero q c hc
  exact ⟨d, hd, markedSpine_cycle_zero_of_normalized_full_image q d hcycle hz⟩

/-- The complete augmentation of every actual capped-cover two-cycle is zero. This
includes all old spine faces as well as the previously proved cap coefficients. -/
theorem cappedCoverCycle_total_augmentation_zero
    (c : (cappedTreeCover q).F →₀ ℤ) (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    Finsupp.mapDomain Prod.snd c = 0 := by
  obtain ⟨d, hd, rfl⟩ := cappedCoverCycle_old_augmentation_zero q c hc
  rw (config := { transparency := .default }) [Finsupp.mapDomain_zero] at hd
  exact hd.symm

end FiniteChains.Davis.Genus
