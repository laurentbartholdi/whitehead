import RequestProject.PresUniversalRelatorGroupCoordinates
import RequestProject.PresUniversalRelatorDeck

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

/-- Actual relator reading coordinates intertwine the actual deck action and left group multiplication. -/
theorem presUniversalRelatorGroupEquiv_deck
    (g : Pi1 (orderCx (PresPos w)) (ptBase w))
    (p : PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w))) :
    presUniversalRelatorGroupEquiv ρ w hw hpos
      (presCoverRelatorMap w uOrderEnd uOrderEnd (uOrderDeckOrderIso g)
        (fun x => endV_deckV g x) p) =
      (readingPresW ρ w hw g * (presUniversalRelatorGroupEquiv ρ w hw hpos p).1,
        (presUniversalRelatorGroupEquiv ρ w hw hpos p).2) := by
  apply Prod.ext
  · exact (presGroupCocycle ρ w hw).readVertex_deck (ptBase w) g p.val.1
  · rfl

/-- Finite actual relator chains transform in the actual group coordinates by left multiplication. -/
theorem presUniversalRelatorGroupChainEquiv_deck
    (g : Pi1 (orderCx (PresPos w)) (ptBase w))
    (c : PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w)) →₀ ℤ) :
    presUniversalRelatorGroupChainEquiv ρ w hw hpos
      (Finsupp.mapDomain
        (presCoverRelatorMap w uOrderEnd uOrderEnd (uOrderDeckOrderIso g)
          (fun x => endV_deckV g x)) c) =
      Finsupp.mapDomain (fun q : PresGroup ρ × J => (readingPresW ρ w hw g * q.1, q.2))
        (presUniversalRelatorGroupChainEquiv ρ w hw hpos c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [Finsupp.mapDomain_add, map_add, hc, hd]
  | single p n =>
    rw [Finsupp.mapDomain_single]
    simp only [presUniversalRelatorGroupChainEquiv, Finsupp.domLCongr_single,
      Finsupp.mapDomain_single, presUniversalRelatorGroupEquiv_deck]

/-- The actual strict two-cycle coordinates respect deck translation in the actual presentation group. -/
theorem presUniversalRelatorChain_group_deck
    (g : Pi1 (orderCx (PresPos w)) (ptBase w))
    (c : StrictOrdTri (UOrder (PresPos w) (ptBase w)) →₀ ℤ) :
    presUniversalRelatorGroupChainEquiv ρ w hw hpos
      (presCoverRelatorChain w uOrderEnd (presUniversalEnd_isPosetCover w hpos) hpos
        (chain2 (strictOrderCxMap (uOrderDeckOrderIso g)
          (uOrderDeckOrderIso g).strictMono) c)) =
      Finsupp.mapDomain (fun q : PresGroup ρ × J => (readingPresW ρ w hw g * q.1, q.2))
        (presUniversalRelatorGroupChainEquiv ρ w hw hpos
          (presCoverRelatorChain w uOrderEnd (presUniversalEnd_isPosetCover w hpos) hpos c)) := by
  rw [presUniversalRelatorChain_deck, presUniversalRelatorGroupChainEquiv_deck]

end FiniteChains.PresModel
