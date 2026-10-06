import RequestProject.StrictOrderNormalizationMaps
import RequestProject.OrderUniversalChainNormalization
import RequestProject.OrderUniversalDeck

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

/-- Actual lifted-order face coordinates commute with the actual path-class deck action. -/
theorem uOrderFace_deck (g : Pi1 (orderCx P) a) (t : OrdTri (UOrder P a)) :
    uOrderFace ((orderCxMap (uOrderDeckOrderIso g) (uOrderDeckOrderIso g).monotone).onF t) =
      deckF g (uOrderFace t) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change (endV (deckV g t.1.1), endV (deckV g t.1.2.1), endV (deckV g t.1.2.2)) =
      (endV t.1.1, endV t.1.2.1, endV t.1.2.2)
    simp only [endV_deckV]

/-- The genuine finite chain equivalence commutes with the actual deck transformations. -/
theorem uOrderChain2Equiv_deck (g : Pi1 (orderCx P) a)
    (c : OrdTri (UOrder P a) →₀ ℤ) :
    uOrderChain2Equiv
      (chain2 (orderCxMap (uOrderDeckOrderIso g) (uOrderDeckOrderIso g).monotone) c) =
      Finsupp.mapDomain (deckF g) (uOrderChain2Equiv c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.mapDomain_add, hc, hd]
  | single t n =>
    change Finsupp.mapDomain uOrderFace
      (Finsupp.mapDomain (orderCxMap (uOrderDeckOrderIso g)
        (uOrderDeckOrderIso g).monotone).onF (Finsupp.single t n)) =
      Finsupp.mapDomain (deckF g) (Finsupp.mapDomain uOrderFace (Finsupp.single t n))
    simp only [Finsupp.mapDomain_single, uOrderFace_deck]

theorem uOrderChain2Equiv_symm_deck (g : Pi1 (orderCx P) a)
    (c : UF (orderCx P) a →₀ ℤ) :
    uOrderChain2Equiv.symm (Finsupp.mapDomain (deckF g) c) =
      chain2 (orderCxMap (uOrderDeckOrderIso g) (uOrderDeckOrderIso g).monotone)
        (uOrderChain2Equiv.symm c) := by
  apply uOrderChain2Equiv.injective
  rw [uOrderChain2Equiv.apply_symm_apply, uOrderChain2Equiv_deck,
    uOrderChain2Equiv.apply_symm_apply]

/-- Genuine normalization of actual cover chains commutes with actual deck transformations. -/
theorem uOrderNormalizeChain2_deck (g : Pi1 (orderCx P) a)
    (c : UF (orderCx P) a →₀ ℤ) :
    uOrderNormalizeChain2 (Finsupp.mapDomain (deckF g) c) =
      chain2 (strictOrderCxMap (uOrderDeckOrderIso g) (uOrderDeckOrderIso g).strictMono)
        (uOrderNormalizeChain2 c) := by
  change normalizeOrdChain2 (uOrderChain2Equiv.symm (Finsupp.mapDomain (deckF g) c)) = _
  rw [uOrderChain2Equiv_symm_deck,
    normalizeOrdChain2_strict_map (uOrderDeckOrderIso g) (uOrderDeckOrderIso g).strictMono]
  rfl

end FiniteChains.Comb
