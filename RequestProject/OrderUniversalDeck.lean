import RequestProject.OrderUniversalPoset

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

/-- Actual deck transformations commute with actual lifted order steps. -/
theorem uOrderStep_deckV (g : Pi1 (orderCx P) a) (v : UOrder P a) (q : P)
    (h : uOrderEnd v ≤ q) :
    uOrderStep (deckV g v) q (by simpa only [uOrderEnd, endV_deckV] using h) =
      deckV g (uOrderStep v q h) := by
  have he : ordPos (by simpa only [uOrderEnd, endV_deckV] using h :
      uOrderEnd (deckV g v) ≤ q) = ordPos h := by
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext (endV_deckV g v) rfl
    · rfl
  unfold uOrderStep
  rw [he, extend_deckV]

/-- The actual deck action preserves the genuine lifted partial order. -/
theorem uOrder_deckV_monotone (g : Pi1 (orderCx P) a) :
    @Monotone (UOrder P a) (UOrder P a)
      (uOrderPartialOrder (P := P) (a := a)).toPreorder
      (uOrderPartialOrder (P := P) (a := a)).toPreorder (deckV g) := by
  intro v z hvz
  obtain ⟨h, he⟩ := hvz
  refine ⟨by simpa only [uOrderEnd, endV_deckV] using h, ?_⟩
  have hs := uOrderStep_deckV g v (uOrderEnd z) h
  simpa only [uOrderEnd, endV_deckV] using hs.trans (congrArg (deckV g) he)

/-- Deck transformations are actual order isomorphisms of the path-class cover. -/
def uOrderDeckOrderIso (g : Pi1 (orderCx P) a) : UOrder P a ≃o UOrder P a where
  toFun := deckV g
  invFun := deckV g⁻¹
  left_inv v := by rw [← deckV_mul, inv_mul_cancel, deckV_one]
  right_inv v := by rw [← deckV_mul, mul_inv_cancel, deckV_one]
  map_rel_iff' {v z} := by
    change UOrderLe (deckV g v) (deckV g z) ↔ UOrderLe v z
    constructor
    · intro h
      have hi := uOrder_deckV_monotone g⁻¹ h
      change UOrderLe (deckV g⁻¹ (deckV g v)) (deckV g⁻¹ (deckV g z)) at hi
      simpa only [← deckV_mul, inv_mul_cancel, deckV_one] using hi
    · exact fun h => uOrder_deckV_monotone g h

/-- The deck action on the actual lifted-order type. -/
def uOrderDeck (g : Pi1 (orderCx P) a) (v : UOrder P a) : UOrder P a := deckV g v

theorem uOrderDeck_end (g : Pi1 (orderCx P) a) (v : UOrder P a) :
    uOrderEnd (uOrderDeck g v) = uOrderEnd v := endV_deckV g v

theorem uOrderDeck_monotone (g : Pi1 (orderCx P) a) : Monotone (uOrderDeck g) :=
  uOrder_deckV_monotone g

end FiniteChains.Comb
