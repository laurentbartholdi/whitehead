import RequestProject.GenusOldAugmentationVanishing
import RequestProject.GenusCappedSpineFox
import RequestProject.TreeCoverAcyclic

/-! Cockcroftness of the actual capped spine, with no geometric input premise. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
open scoped Classical
variable (q : ℕ) [NeZero q]

/-- Collapsing the spanning tree reflects the two-cycle condition. -/
theorem cappedPresentationCycle_treeCycle
    (c : (univCover (cappedSpinePresentation q)).F →₀ ℤ)
    (hc : Comb.bdry2 (univCover (cappedSpinePresentation q)) c = 0) :
    Comb.bdry2 (cappedTreeCover q) c = 0 := by
  let T := cappedSpineTree q
  let N := relSub (cappedSpinePresentation q)
  have hN : ∀ f, SpanningTree.treeRel T f ∈ N := by
    intro f
    rw (config := { transparency := .default }) [cappedSpineTree_rel]
    exact rel_mem_relSub (cappedSpinePresentation q) f
  have hp : SpanningTree.piE T N (Comb.bdry2 (cappedTreeCover q) c) = 0 := by
    rw (config := { transparency := .default }) [SpanningTree.piE_bdry2 (hN := hN)]
    change Comb.bdry2 (coverComplex N (SpanningTree.treeRel (cappedSpineTree q)) hN) c = 0
    have hrel : SpanningTree.treeRel (cappedSpineTree q) = cappedSpinePresentation q :=
      cappedSpineTree_rel q
    change Finsupp.linearCombination ℤ
      (fun f => pathChain (liftPath
        (FreeGroup.toWord (SpanningTree.treeRel (cappedSpineTree q) f.2)) f.1)) c = 0
    rw (config := { transparency := .default }) [hrel]
    exact hc
  exact SpanningTree.treeChain_eq_zero (T := T) (N := N) (hN := hN)
    (SpanningTree.support_isTree_of_piE_eq_zero (T := T) (N := N) hp)
    (Comb.bdry1_bdry2 (X := cappedTreeCover q) c)

/-- The genuine capped presentation is Cockcroft. -/
theorem cappedSpinePresentation_isCockcroft :
    _root_.FiniteChains.IsCockcroft (cappedSpinePresentation q) := by
  apply (coverCycles_cockcroft_iff (cappedSpinePresentation q)).mp
  intro c hc
  exact cappedCoverCycle_total_augmentation_zero q c
    (cappedPresentationCycle_treeCycle q c hc)

/-- The actual capped-spine complex is Cockcroft. -/
theorem cappedSpine_isCockcroft : Comb.IsCockcroft (cappedSpineCx q) :=
  (cappedSpine_cockcroft_iff_fox q).mpr (cappedSpinePresentation_isCockcroft q)

end FiniteChains.Davis.Genus
