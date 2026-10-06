module

public import RequestProject.PresUniversalFoxKernelEquiv
public import RequestProject.PresUniversalGroupCoordinatesDeck

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

/-- Actual deck translation is actual group-ring multiplication in relator-ring coordinates. -/
theorem presUniversalRelatorRingEquiv_deck
    (g : Pi1 (orderCx (PresPos w)) (ptBase w))
    (c : PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w)) →₀ ℤ) :
    presUniversalRelatorRingEquiv ρ w hw hpos
      (Finsupp.mapDomain
        (presCoverRelatorMap w uOrderEnd uOrderEnd (uOrderDeckOrderIso g)
          (fun x => endV_deckV g x)) c) =
      MonoidAlgebra.single (readingPresW ρ w hw g) (1 : ℤ) •
        presUniversalRelatorRingEquiv ρ w hw hpos c := by
  change groupCellChainEquiv (presUniversalRelatorGroupChainEquiv ρ w hw hpos _) = _
  rw [presUniversalRelatorGroupChainEquiv_deck, groupCellChainEquiv_left_translate]
  rfl

/-- The genuine triangle-chain/Fox relator coordinate map respects the actual deck group action. -/
theorem presUniversalRelatorChain_ring_deck
    (g : Pi1 (orderCx (PresPos w)) (ptBase w))
    (c : StrictOrdTri (UOrder (PresPos w) (ptBase w)) →₀ ℤ) :
    presUniversalRelatorRingEquiv ρ w hw hpos
      (presCoverRelatorChain w uOrderEnd (presUniversalEnd_isPosetCover w hpos) hpos
        (chain2 (strictOrderCxMap (uOrderDeckOrderIso g)
          (uOrderDeckOrderIso g).strictMono) c)) =
      MonoidAlgebra.single (readingPresW ρ w hw g) (1 : ℤ) •
        presUniversalRelatorRingEquiv ρ w hw hpos
          (presCoverRelatorChain w uOrderEnd (presUniversalEnd_isPosetCover w hpos) hpos c) := by
  rw [presUniversalRelatorChain_deck, presUniversalRelatorRingEquiv_deck]

end FiniteChains.PresModel
