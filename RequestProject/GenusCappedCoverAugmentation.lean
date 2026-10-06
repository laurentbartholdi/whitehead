import RequestProject.GenusCappedCoverChainMap
import RequestProject.UniversalThreeAugmentation

/-! The exact deck-forgetting formula for the constructed capped-cover comparison. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
open scoped Classical
variable (q : ℕ) [NeZero q]

noncomputable def rootedAugmentedFace : (cappedSpineCx q).F →
    (orderCx (QCube (cmpRel (GenusVertex q)))).F →₀ ℤ
  | .inl f => Finsupp.single ((markedSpineToFullCube q).onF f) 1
  | .inr x => hurewicz _ ((markedSpineToFullCube q).onV (markedSpineTree q).root)
      (rootedBaseCapFilling q x)

noncomputable def rootedAugmentedChain2 :
    ((cappedSpineCx q).F →₀ ℤ) →ₗ[ℤ]
      ((orderCx (QCube (cmpRel (GenusVertex q)))).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (rootedAugmentedFace q)

/-- The constructed full comparison commutes with forgetting the actual deck coordinate. -/
theorem rootedCoverChain2_hurewicz (c : (cappedTreeCover q).F →₀ ℤ) :
    hurewicz _ ((markedSpineToFullCube q).onV (markedSpineTree q).root)
      (rootedCoverChain2 q c) = rootedAugmentedChain2 q (Finsupp.mapDomain Prod.snd c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      rw (config := { transparency := .default }) [map_add, map_add, hc, hd, Finsupp.mapDomain_add, map_add]
  | single gf n =>
      rw (config := { transparency := .default }) [rootedCoverChain2, Finsupp.linearCombination_single, map_smul,
        Finsupp.mapDomain_single, rootedAugmentedChain2, Finsupp.linearCombination_single]
      congr 1
      obtain ⟨g, f | x⟩ := gf
      · change Finsupp.mapDomain (univProj _ _).onF
          (Finsupp.single (rootedOldFace q g f) 1) =
          Finsupp.single ((markedSpineToFullCube q).onF f) 1
        rw (config := { transparency := .default }) [Finsupp.mapDomain_single]
        rfl
      · exact hurewicz_deck_faceChains _ _ _

/-- The augmented comparison of a genuine capped-cover cycle is an actual three-boundary. -/
theorem rootedAugmentedCycle_boundary3 (c : (cappedTreeCover q).F →₀ ℤ)
    (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ y : OrdTet (QCube (cmpRel (GenusVertex q))) →₀ ℤ,
      ordBoundary3 y = rootedAugmentedChain2 q (Finsupp.mapDomain Prod.snd c) := by
  obtain ⟨z, hz⟩ := rootedCoverCycle_fullCube_filling q c hc
  refine ⟨Finsupp.mapDomain (fun t => t.1.2) z, ?_⟩
  rw (config := { transparency := .default }) [← hurewicz_uOrdBoundary3, hz, rootedCoverChain2_hurewicz]

end FiniteChains.Davis.Genus
