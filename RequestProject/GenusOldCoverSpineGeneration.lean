module

public import RequestProject.GenusOldCoverSpineFaithfulness

@[expose] public section

/-!
Actual chain generation and reference-filling adjustment in every old-cell
cover. The cycle-generation hypothesis is supplied by the proved geometric
collapse of the truncated block, rather than assumed of the old cover.

Written proof terms; no verification has been run under the current workflow.
-/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] (f : P → QOld (cmpRel (GenusVertex q)))

/-- Every homogeneous old-cover two-cycle is represented by an actual cycle on
the actual covered spine, modulo an actual increasing three-boundary. -/
theorem genus_old_cover_spine_nerve_generation (hf : IsPosetCover f)
    (z : Ch P) (hz : z ∈ Inc P) (hd : lengthProjection 3 z = z)
    (hcyc : Nerve.bdry z = 0) :
    ∃ c ∈ Inc (OldCoveredSpine q f), lengthProjection 3 c = c ∧
      Nerve.bdry c = 0 ∧ ∃ y ∈ Inc P,
        z = cmap (oldCoveredSpineToOld q f) c + Nerve.bdry y := by
  let B := fun p : TruncatedCover f => truncatedCoverProjection f p ∈ genusSpineCellSet q
  let s := truncatedCoverSection f
  let r := truncatedCoverRetraction f
  let z' := cmap s z
  have hs := truncatedCoverSection_monotone f hf.mono
  have hr := posetPullbackOriginal_monotone f truncatedCellRetraction
  have hz' : z' ∈ IncOn (fun _ : TruncatedCover f => True) :=
    cmap_mem_incOn_of_maps hs (fun _ => True.intro) hz
  have hd' : lengthProjection 3 z' = z' := by
    rw (config := { transparency := .default }) [lengthProjection_cmap, hd]
  have hcyc' : Nerve.bdry z' = 0 := by
    rw (config := { transparency := .default }) [← cmap_bdry, hcyc, map_zero]
  obtain ⟨c₀, hc₀, y₀, hy₀, hcc₀, he₀⟩ :=
    (genusSpine_cover_homology q (truncatedCoverProjection_isPosetCover f hf)).1
      z' hz' hd' hcyc'
  let b := lengthProjection 3 c₀
  let y := lengthProjection 4 y₀
  have hb : b ∈ IncOn B := lengthProjection_mem_incOn _ hc₀
  have hy : y ∈ Inc (TruncatedCover f) :=
    lengthProjection_mem_inc _ (incOn_le_inc _ hy₀)
  have hbd : lengthProjection 3 b = b := lengthProjection_idempotent _ _
  have hbc : Nerve.bdry b = 0 := by
    rw (config := { transparency := .default }) [← lengthProjection_bdry, hcc₀, map_zero]
  have he : z' = b + Nerve.bdry y := by
    rw (config := { transparency := .default }) [← hd', he₀, map_add, lengthProjection_bdry]
  have hne : ∃ p : TruncatedCover f, B p := by
    obtain ⟨p, hp⟩ := (truncatedCoverProjection_isPosetCover f hf).surj (spineBase q).1
    refine ⟨p, ?_⟩
    change truncatedCoverProjection f p ∈ genusSpineCellSet q
    rw (config := { transparency := .default }) [hp]
    exact (spineBase q).2
  obtain ⟨c, hc, hcb⟩ := exists_preimage_of_mem_incOn B hb
  have hcd : lengthProjection 3 c = c := by
    apply cmap_val_injective B hne
    rw (config := { transparency := .default }) [← lengthProjection_cmap, hcb, hbd]
  have hcc : Nerve.bdry c = 0 := by
    apply cmap_val_injective B hne
    rw (config := { transparency := .default }) [cmap_bdry, hcb, hbc, map_zero]
  refine ⟨c, hc, hcd, hcc, cmap r y, cmap_mem_inc_of_monotone hr hy, ?_⟩
  have hp := congrArg (cmap r) he
  have hreturn : cmap r z' = z := by
    rw (config := { transparency := .default }) [cmap_comp]
    change cmap id z = z
    exact cmap_id z
  rw (config := { transparency := .default }) [hreturn, map_add, cmap_bdry, ← hcb, cmap_comp] at hp
  exact hp

/-- The preceding geometric representative can be made strictly cellular.
Degenerate flags are removed with the explicit normalization three-chain. -/
theorem genus_old_cover_spine_cycle_generation (hf : IsPosetCover f)
    (z : Ch P) (hz : z ∈ Inc P) (hd : lengthProjection 3 z = z)
    (hcyc : Nerve.bdry z = 0) :
    ∃ c : StrictOrdTri (OldCoveredSpine q f) →₀ ℤ,
      Comb.bdry2 (strictOrderCx (OldCoveredSpine q f)) c = 0 ∧
      ∃ y ∈ Inc P, z = cmap (oldCoveredSpineToOld q f)
        (ordNerveChain2 (ordStrictInclusion2 c)) + Nerve.bdry y := by
  obtain ⟨b, hb, hbd, hbc, y, hy, he⟩ :=
    genus_old_cover_spine_nerve_generation q f hf z hz hd hcyc
  let a := decodeOrdNerve2 b
  have ha : ordNerveChain2 a = b := by
    rw (config := { transparency := .default }) [ordNerveChain2_decode hb, hbd]
  have hac : Comb.bdry2 (orderCx (OldCoveredSpine q f)) a = 0 :=
    (ordNerveChain2_cycle_iff a).mp (by rw (config := { transparency := .default }) [ha]; exact hbc)
  let w := ordNerveChain3 (ordNormalizationHomotopy2 a)
  have hw : w ∈ Inc (OldCoveredSpine q f) := ordNerveChain3_mem_inc _
  have hwb : b - ordNerveChain2 (ordStrictInclusion2 (normalizeOrdChain2 a)) =
      Nerve.bdry w := by
    rw (config := { transparency := .default }) [← ha]
    exact ordNerve_normalization_cycle a hac
  let g := oldCoveredSpineToOld q f
  have hg := oldCoveredSpineToOld_monotone q f
  refine ⟨normalizeOrdChain2 a, normalizeOrdChain2_cycle a hac,
    cmap g w + y, (Inc _).add_mem (cmap_mem_inc_of_monotone hg hw) hy, ?_⟩
  rw (config := { transparency := .default }) [map_add, ← cmap_bdry, ← hwb, map_sub, he]
  abel

/-- Any spine filling can be adjusted by an actual spine cycle so that its
old-cover realization represents a prescribed geometric filling of the same
boundary. This is the normalization needed when choosing the marked reference
filling before arbitrary substitutions. -/
theorem genus_old_cover_spine_adjust_filling (hf : IsPosetCover f)
    (d : StrictOrdTri (OldCoveredSpine q f) →₀ ℤ)
    (z : Ch P) (hz : z ∈ Inc P) (hd : lengthProjection 3 z = z)
    (hb : Nerve.bdry z = Nerve.bdry (cmap (oldCoveredSpineToOld q f)
      (ordNerveChain2 (ordStrictInclusion2 d)))) :
    ∃ d' : StrictOrdTri (OldCoveredSpine q f) →₀ ℤ,
      Comb.bdry2 (strictOrderCx (OldCoveredSpine q f)) d' =
        Comb.bdry2 (strictOrderCx (OldCoveredSpine q f)) d ∧
      ∃ y ∈ Inc P, z = cmap (oldCoveredSpineToOld q f)
        (ordNerveChain2 (ordStrictInclusion2 d')) + Nerve.bdry y := by
  let g := oldCoveredSpineToOld q f
  let b := cmap g (ordNerveChain2 (ordStrictInclusion2 d))
  have hbi : b ∈ Inc P := cmap_mem_inc_of_monotone
    (oldCoveredSpineToOld_monotone q f) (ordNerveChain2_mem_inc _)
  have hbd : lengthProjection 3 b = b := by
    rw (config := { transparency := .default }) [lengthProjection_cmap, ordNerveChain2_lengthProjection]
  have hzd : lengthProjection 3 (z - b) = z - b := by
    rw (config := { transparency := .default }) [map_sub, hd, hbd]
  have hzc : Nerve.bdry (z - b) = 0 := by
    rw (config := { transparency := .default }) [map_sub, hb, sub_self]
  obtain ⟨c, hc, y, hy, he⟩ := genus_old_cover_spine_cycle_generation q f hf
    (z - b) ((Inc _).sub_mem hz hbi) hzd hzc
  refine ⟨d + c, ?_, y, hy, ?_⟩
  · rw (config := { transparency := .default }) [map_add, hc, add_zero]
  · simp only [map_add]
    have he' := congrArg (fun x : Ch P => x + b) he
    simp only [sub_add_cancel] at he'
    rw (config := { transparency := .default }) [he']
    dsimp only [b]
    abel

/-- The geometric normalization is unique as an actual strict spine chain.
The old-cover comparison reflects the difference boundary, so no second
homology vanishing assertion is required. -/
theorem genus_old_cover_spine_adjust_filling_unique (hf : IsPosetCover f)
    (d : StrictOrdTri (OldCoveredSpine q f) →₀ ℤ)
    (z : Ch P) (hz : z ∈ Inc P) (hd : lengthProjection 3 z = z)
    (hb : Nerve.bdry z = Nerve.bdry (cmap (oldCoveredSpineToOld q f)
      (ordNerveChain2 (ordStrictInclusion2 d)))) :
    ∃! d' : StrictOrdTri (OldCoveredSpine q f) →₀ ℤ,
      Comb.bdry2 (strictOrderCx (OldCoveredSpine q f)) d' =
        Comb.bdry2 (strictOrderCx (OldCoveredSpine q f)) d ∧
      ∃ y ∈ Inc P, z = cmap (oldCoveredSpineToOld q f)
        (ordNerveChain2 (ordStrictInclusion2 d')) + Nerve.bdry y := by
  obtain ⟨d', hd', yd, hyd, hed⟩ := genus_old_cover_spine_adjust_filling q f hf d z hz hd hb
  refine ⟨d', ⟨hd', yd, hyd, hed⟩, ?_⟩
  rintro e ⟨he, ye, hye, hee⟩
  apply sub_eq_zero.mp
  apply genus_old_cover_spine_chain_zero_of_boundary q f hf (e - d')
  · rw (config := { transparency := .default }) [map_sub, he, hd', sub_self]
  · refine ⟨yd - ye, (Inc _).sub_mem hyd hye, ?_⟩
    have hbd : Nerve.bdry yd = z - cmap (oldCoveredSpineToOld q f)
        (ordNerveChain2 (ordStrictInclusion2 d')) := by
      rw (config := { transparency := .default }) [hed]
      abel
    have hbe : Nerve.bdry ye = z - cmap (oldCoveredSpineToOld q f)
        (ordNerveChain2 (ordStrictInclusion2 e)) := by
      rw (config := { transparency := .default }) [hee]
      abel
    rw (config := { transparency := .default }) [map_sub, hbd, hbe]
    simp only [map_sub]
    abel

end FiniteChains.Davis.Genus
