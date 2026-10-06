module

public import RequestProject.PresUniversalCockcroftCoordinates
public import RequestProject.PresCoverCyclePushdownZero
public import RequestProject.StrictOrderNormalizationMaps
public import RequestProject.OrderNormalizationHomotopy

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} [DecidableEq α] [Fintype J]
  (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

include hw in
/-- The actual weak universal cycle pushdown of a Cockcroft presentation has
an explicit genuine order-nerve three-filling. -/
theorem presUniversalCockcroft_weak_pushdown_boundary (hC : IsCockcroft ρ)
    (c : OrdTri (UOrder (PresPos w) (ptBase w)) →₀ ℤ)
    (hc : Comb.bdry2 (orderCx (UOrder (PresPos w) (ptBase w))) c = 0) :
    chain2 (orderCxMap uOrderEnd (presUniversalEnd_isPosetCover w hpos).mono) c =
      ordBoundary3 (ordNormalizationHomotopy2
        (chain2 (orderCxMap uOrderEnd (presUniversalEnd_isPosetCover w hpos).mono) c)) := by
  let f := uOrderEnd (P := PresPos w) (a := ptBase w)
  let hf := presUniversalEnd_isPosetCover w hpos
  have hn : Comb.bdry2 (strictOrderCx (UOrder (PresPos w) (ptBase w)))
      (normalizeOrdChain2 c) = 0 := normalizeOrdChain2_cycle c hc
  have ha := presUniversalCockcroft_relator_augmentation_zero ρ w hw hpos hC
    ⟨normalizeOrdChain2 c, hn⟩
  have hs := presCover_cycle_pushdown_zero w f hf hpos (normalizeOrdChain2 c) hn ha
  have hz : normalizeOrdChain2 (chain2 (orderCxMap f hf.mono) c) = 0 := by
    rw (config := { transparency := .default }) [normalizeOrdChain2_map, normalizedStrictChain2_eq_strict]
    exact hs
  have hp : Comb.bdry2 (orderCx (PresPos w)) (chain2 (orderCxMap f hf.mono) c) = 0 := by
    rw (config := { transparency := .default }) [bdry2_chain2, hc, map_zero]
  have h := ordNormalization_cycle_boundary (chain2 (orderCxMap f hf.mono) c) hp
  rw (config := { transparency := .default }) [hz, map_zero, sub_zero] at h
  exact h

end FiniteChains.PresModel
