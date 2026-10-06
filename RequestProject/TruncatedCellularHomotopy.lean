module

public import RequestProject.TruncatedCubePi1
public import RequestProject.OrderNerveCellMaps

@[expose] public section

/-! The actual truncation prism in cellular degrees two and three. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

theorem exists_truncated_cellular_retraction_homotopy
    (c : (orderCx (TruncatedCell A)).F →₀ ℤ)
    (hc : Comb.bdry2 (orderCx (TruncatedCell A)) c = 0) :
    ∃ y : OrdTet (TruncatedCell A) →₀ ℤ,
      ordBoundary3 y =
        chain2 (orderCxMap (oldCellIncl ∘ truncatedCellRetraction)
          (oldCellIncl_monotone.comp truncatedCellRetraction_monotone)) c - c := by
  let g : TruncatedCell A → TruncatedCell A := oldCellIncl ∘ truncatedCellRetraction
  have hg : Monotone g := oldCellIncl_monotone.comp truncatedCellRetraction_monotone
  obtain ⟨b, hb, hdeg, hbdry⟩ := truncated_cycle_retraction_boundary 3 (ordNerveChain2 c)
    (ordNerveChain2_mem_inc c) ((ordNerveChain2_cycle_iff c).mpr hc)
    (ordNerveChain2_lengthProjection c)
  refine ⟨decodeOrdNerve3 b, ?_⟩
  apply ordNerveChain2_injective
  rw (config := { transparency := .default }) [ordNerveChain2_ordBoundary3, ordNerveChain3_decode hb, hdeg, map_sub]
  rw (config := { transparency := .default }) [hbdry]
  change Nerve.lengthProjection 3 (Nerve.cmap g (ordNerveChain2 c)) - ordNerveChain2 c = _
  rw (config := { transparency := .default }) [← ordNerveChain2_chain2 g hg, ordNerveChain2_lengthProjection]

/-- Truncation reflects actual full-nerve two-boundaries, without an exactness premise. -/
theorem truncatedRetraction_reflects_boundary3
    (c : (orderCx (TruncatedCell A)).F →₀ ℤ)
    (hc : Comb.bdry2 (orderCx (TruncatedCell A)) c = 0)
    (h : ∃ z : OrdTet (QOld A) →₀ ℤ,
      ordBoundary3 z = chain2 truncatedRetractionHom c) :
    ∃ y : OrdTet (TruncatedCell A) →₀ ℤ, ordBoundary3 y = c := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨w, hw⟩ := exists_truncated_cellular_retraction_homotopy c hc
  refine ⟨Finsupp.mapDomain (ordTetMap oldCellIncl oldCellIncl_monotone) z - w, ?_⟩
  rw (config := { transparency := .default }) [map_sub, ← chain2_ordBoundary3, hz, hw]
  have he : chain2 (orderCxMap oldCellIncl oldCellIncl_monotone)
      (chain2 truncatedRetractionHom c) =
      chain2 (orderCxMap (oldCellIncl ∘ truncatedCellRetraction)
        (oldCellIncl_monotone.comp truncatedCellRetraction_monotone)) c := by
    change Finsupp.mapDomain (orderCxMap oldCellIncl oldCellIncl_monotone).onF
      (Finsupp.mapDomain truncatedRetractionHom.onF c) = _
    rw (config := { transparency := .default }) [← Finsupp.mapDomain_comp]
    rfl
  rw (config := { transparency := .default }) [he]
  abel

end FiniteChains.Davis
