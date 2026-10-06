import RequestProject.GenusSurfaceCharacters

/-! Reduction of capped-cover augmentation to actual old spine faces. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem exists_oldFaceChain_of_caps_zero (c : (cappedSpineCx q).F →₀ ℤ)
    (hc : ∀ x : Fin q × Bool, c (.inr x) = 0) :
    ∃ d : (markedSpineCx q).F →₀ ℤ, Finsupp.mapDomain Sum.inl d = c := by
  refine ⟨c.comapDomain Sum.inl Sum.inl_injective.injOn, ?_⟩
  apply Finsupp.mapDomain_comapDomain _ Sum.inl_injective
  intro f hf
  obtain f | x := f
  · exact ⟨f, rfl⟩
  · exact False.elim ((Finsupp.mem_support_iff.mp hf) (hc x))

theorem controlledAugmentedChain2_old (d : (markedSpineCx q).F →₀ ℤ) :
    controlledAugmentedChain2 q (Finsupp.mapDomain Sum.inl d) =
      chain2 (markedSpineToFullCube q) d := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw (config := { transparency := .default }) [Finsupp.mapDomain_add, map_add, hc, hd, map_add]
  | single f n =>
      rw (config := { transparency := .default }) [Finsupp.mapDomain_single, controlledAugmentedChain2,
        Finsupp.linearCombination_single]
      change n • Finsupp.single ((markedSpineToFullCube q).onF f) 1 =
        Finsupp.mapDomain (markedSpineToFullCube q).onF (Finsupp.single f n)
      simp

/-- Every actual capped-cover cycle augments entirely into old spine faces, whose
full-cube image is an actual ordinary three-boundary. -/
theorem cappedCoverCycle_old_augmentation (c : (cappedTreeCover q).F →₀ ℤ)
    (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ d : (markedSpineCx q).F →₀ ℤ,
      Finsupp.mapDomain Sum.inl d = Finsupp.mapDomain Prod.snd c ∧
      ∃ y : OrdTet (QCube (cmpRel (GenusVertex q))) →₀ ℤ,
        ordBoundary3 y = chain2 (markedSpineToFullCube q) d := by
  obtain ⟨d, hd⟩ := exists_oldFaceChain_of_caps_zero q (Finsupp.mapDomain Prod.snd c)
    (cappedCoverCycle_cap_augmentation_zero q c hc)
  obtain ⟨y, hy⟩ := controlledAugmentedCycle_boundary3 q c hc
  refine ⟨d, hd, y, ?_⟩
  rw (config := { transparency := .default }) [← hd, controlledAugmentedChain2_old] at hy
  exact hy

theorem cappedCoverCycle_old_augmentation_cycle (c : (cappedTreeCover q).F →₀ ℤ)
    (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ d : (markedSpineCx q).F →₀ ℤ,
      Finsupp.mapDomain Sum.inl d = Finsupp.mapDomain Prod.snd c ∧
      Comb.bdry2 (markedSpineCx q) d = 0 ∧
      ∃ y : OrdTet (QCube (cmpRel (GenusVertex q))) →₀ ℤ,
        ordBoundary3 y = chain2 (markedSpineToFullCube q) d := by
  obtain ⟨d, hd, y, hy⟩ := cappedCoverCycle_old_augmentation q c hc
  have hp : Comb.bdry2 (cappedSpineCx q) (Finsupp.mapDomain Prod.snd c) = 0 := by
    let f : Hom (cappedTreeCover q) (cappedSpineCx q) :=
      SpanningTree.treeCoverProj (cappedSpineTree q) (relSub (cappedSpinePresentation q)) _
    change Comb.bdry2 (cappedSpineCx q) (chain2 f c) = 0
    rw (config := { transparency := .default }) [bdry2_chain2, hc, map_zero]
  rw (config := { transparency := .default }) [← hd] at hp
  change Comb.bdry2 (cappedSpineCx q) (chain2 (cappedSpineIncl q) d) = 0 at hp
  rw (config := { transparency := .default }) [bdry2_chain2] at hp
  have hzero : Comb.bdry2 (markedSpineCx q) d = 0 := by
    convert hp using 1 <;>
      simp only [chain1, cappedSpineIncl, Finsupp.lmapDomain_apply, Finsupp.mapDomain_id]
  exact ⟨d, hd, hzero, y, hy⟩

end FiniteChains.Davis.Genus
