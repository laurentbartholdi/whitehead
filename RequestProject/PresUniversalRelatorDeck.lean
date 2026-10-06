module

public import RequestProject.PresCoverRelatorNaturality
public import RequestProject.OrderUniversalDeck
public import RequestProject.OrderUniversalPosetCover
public import RequestProject.PresPosetConnected

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool))
  (hpos : ∀ j, 0 < (w j).length)

include hpos

/-- The actual path-class cover projection of the nonempty-word presentation model. -/
theorem presUniversalEnd_isPosetCover :
    IsPosetCover (uOrderEnd (P := PresPos w) (a := ptBase w)) := by
  apply uOrderEnd_isPosetCover
  apply presPos_isConnected w
  intro j he
  have h := hpos j
  rw [he, List.length_nil] at h
  omega

/-- Actual universal-cover relator coordinates transform by the actual deck action. -/
theorem presUniversalRelatorChain_deck
    (g : Pi1 (orderCx (PresPos w)) (ptBase w))
    (c : StrictOrdTri (UOrder (PresPos w) (ptBase w)) →₀ ℤ) :
    presCoverRelatorChain w uOrderEnd (presUniversalEnd_isPosetCover w hpos) hpos
      (chain2 (strictOrderCxMap (uOrderDeckOrderIso g)
        (uOrderDeckOrderIso g).strictMono) c) =
    Finsupp.mapDomain
      (presCoverRelatorMap w uOrderEnd uOrderEnd (uOrderDeckOrderIso g)
        (fun x => endV_deckV g x))
      (presCoverRelatorChain w uOrderEnd (presUniversalEnd_isPosetCover w hpos) hpos c) := by
  exact presCoverRelatorChain_natural w uOrderEnd
    (presUniversalEnd_isPosetCover w hpos) hpos uOrderEnd
    (presUniversalEnd_isPosetCover w hpos) (uOrderDeckOrderIso g)
    (uOrderDeckOrderIso g).strictMono (uOrderDeckOrderIso g).injective
    (uOrderDeckOrderIso g).surjective (fun x => endV_deckV g x) c

end FiniteChains.PresModel
