import RequestProject.TruncatedCoverRetraction
import RequestProject.GenusCoveredSpineCycleFaithfulness

/-! Actual covered-spine cycles are detected in the old cubical block. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] (f : P → QOld (cmpRel (GenusVertex q)))

abbrev OldCoveredSpine :=
  {p : TruncatedCover f // truncatedCoverProjection f p ∈ genusSpineCellSet q}

def oldCoveredSpineToOld (p : OldCoveredSpine q f) : P := truncatedCoverRetraction f p.1

theorem oldCoveredSpineToOld_monotone : Monotone (oldCoveredSpineToOld q f) :=
  fun _ _ h => h.1

/-- The comparison is constructed in the pullback of the actual covering.
It detects a boundary after projecting to old cells, without assuming an
isomorphism of covered chain complexes. -/
theorem genus_old_cover_spine_chain_zero_of_boundary (hf : IsPosetCover f)
    (c : StrictOrdTri (OldCoveredSpine q f) →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx (OldCoveredSpine q f)) c = 0)
    (hbound : ∃ y ∈ Inc P, Nerve.bdry y =
      cmap (oldCoveredSpineToOld q f) (ordNerveChain2 (ordStrictInclusion2 c))) : c = 0 := by
  have hp := truncatedCoverProjection_isPosetCover f hf
  apply genus_covered_spine_chain_zero_of_boundary q hp c
  let z := cmap (Subtype.val : OldCoveredSpine q f → TruncatedCover f)
    (ordNerveChain2 (ordStrictInclusion2 c))
  have hz : z ∈ Inc (TruncatedCover f) :=
    cmap_mem_inc_of_monotone monotone_subtypeVal (ordNerveChain2_mem_inc _)
  have hweak : Comb.bdry2 (orderCx (OldCoveredSpine q f)) (ordStrictInclusion2 c) = 0 := by
    change Comb.bdry2 _ (chain2 (strictOrderIncl _) c) = 0
    rw [bdry2_chain2, hc, map_zero]
  have hcyc : Nerve.bdry z = 0 := by
    rw [← cmap_bdry, (ordNerveChain2_cycle_iff _).mpr hweak, map_zero]
  apply truncatedCoverRetraction_reflects_boundaries f hf.mono z hz hcyc
  change ∃ y ∈ Inc P, Nerve.bdry y =
    cmap (fun x : OldCoveredSpine q f => truncatedCoverRetraction f x.val)
      (ordNerveChain2 (ordStrictInclusion2 c)) at hbound
  simpa only [z, cmap_comp, oldCoveredSpineToOld, Function.comp_def] using hbound

/-- Equivalent concrete input using an actual finite chain of old-cell tetrahedra. -/
theorem genus_old_cover_spine_chain_zero_of_cellular_boundary (hf : IsPosetCover f)
    (c : StrictOrdTri (OldCoveredSpine q f) →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx (OldCoveredSpine q f)) c = 0)
    (hbound : ∃ y : OrdTet P →₀ ℤ, ordBoundary3 y =
      chain2 (orderCxMap (oldCoveredSpineToOld q f) (oldCoveredSpineToOld_monotone q f))
        (ordStrictInclusion2 c)) : c = 0 := by
  apply genus_old_cover_spine_chain_zero_of_boundary q f hf c hc
  obtain ⟨y, hy⟩ := hbound
  refine ⟨ordNerveChain3 y, ordNerveChain3_mem_inc y, ?_⟩
  rw [← ordNerveChain2_ordBoundary3, hy, ordNerveChain2_chain2]

end FiniteChains.Davis.Genus
