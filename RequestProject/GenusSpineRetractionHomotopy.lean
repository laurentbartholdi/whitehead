module

public import RequestProject.GenusSpineRetraction
public import RequestProject.TruncatedCellularHomotopy

@[expose] public section

/-! The actual retained-cube retraction fixes spine two-cycles after normalization. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem genusSpine_strict_three_flags_empty : IsEmpty (StrictOrdTet (GenusSpineCell q)) := by
  refine ⟨fun t => ?_⟩
  have h01 := genusSpineCellDimension_strictMono q t.2.1
  have h12 := genusSpineCellDimension_strictMono q t.2.2.1
  have h23 := genusSpineCellDimension_strictMono q t.2.2.2
  change truncatedCellDimension t.1.1.1 < truncatedCellDimension t.1.2.1.1 at h01
  change truncatedCellDimension t.1.2.1.1 < truncatedCellDimension t.1.2.2.1.1 at h12
  change truncatedCellDimension t.1.2.2.1.1 < truncatedCellDimension t.1.2.2.2.1 at h23
  have hmax := genusSpineCell_dimension_le_two q t.1.2.2.2
  omega

/-- The actual pointwise order comparison supplies a finite full-nerve homotopy chain. -/
theorem genusSpine_cycle_retraction_boundary (c : (orderCx (GenusSpineCell q)).F →₀ ℤ)
    (hc : Comb.bdry2 (orderCx (GenusSpineCell q)) c = 0) :
    ∃ y : OrdTet (GenusSpineCell q) →₀ ℤ, ordBoundary3 y =
      chain2 (orderCxMap (genusSpineRetraction q) (genusSpineRetraction_monotone q)) c - c := by
  let g := genusSpineRetraction q
  let p := Nerve.prism id g (ordNerveChain2 c)
  have hp : p ∈ Nerve.Inc (GenusSpineCell q) :=
    Nerve.prism_mem_inc monotone_id (genusSpineRetraction_monotone q)
      (genusSpine_le_retraction q) (ordNerveChain2_mem_inc c)
  have hd := (ordNerveChain2_cycle_iff c).mpr hc
  have hb : Nerve.bdry p = Nerve.cmap g (ordNerveChain2 c) - ordNerveChain2 c := by
    simpa [p, hd] using Nerve.bdry_prism_add_prism_bdry id g (ordNerveChain2 c)
  let b := Nerve.lengthProjection 4 p
  have hbi : b ∈ Nerve.Inc (GenusSpineCell q) := Nerve.lengthProjection_mem_inc _ hp
  have hdeg : Nerve.lengthProjection 4 b = b := Nerve.lengthProjection_idempotent _ _
  have hbdry : Nerve.bdry b = Nerve.lengthProjection 3
      (Nerve.cmap g (ordNerveChain2 c)) - ordNerveChain2 c := by
    dsimp only [b]
    rw (config := { transparency := .default }) [← Nerve.lengthProjection_bdry, hb, map_sub, ordNerveChain2_lengthProjection]
  refine ⟨decodeOrdNerve3 b, ?_⟩
  apply ordNerveChain2_injective
  rw (config := { transparency := .default }) [ordNerveChain2_ordBoundary3, ordNerveChain3_decode hbi, hdeg, map_sub, hbdry]
  rw (config := { transparency := .default }) [← ordNerveChain2_chain2 g (genusSpineRetraction_monotone q),
    ordNerveChain2_lengthProjection]

/-- On the actual two-dimensional surviving spine, the retained-cube retraction fixes
normalized two-cycles exactly because there are no nondegenerate three-flags. -/
theorem genusSpine_normalized_retraction_cycle (c : (orderCx (GenusSpineCell q)).F →₀ ℤ)
    (hc : Comb.bdry2 (orderCx (GenusSpineCell q)) c = 0) :
    normalizeOrdChain2
      (chain2 (orderCxMap (genusSpineRetraction q) (genusSpineRetraction_monotone q)) c) =
      normalizeOrdChain2 c := by
  obtain ⟨y, hy⟩ := genusSpine_cycle_retraction_boundary q c hc
  haveI := genusSpine_strict_three_flags_empty q
  have hzero : normalizeOrdChain3 y = 0 := by
    ext t
    exact isEmptyElim t
  have he := congrArg normalizeOrdChain2 hy
  rw (config := { transparency := .default }) [normalizeOrdChain2_ordBoundary3, hzero, map_zero, map_sub] at he
  exact (sub_eq_zero.mp he.symm)

end FiniteChains.Davis.Genus
