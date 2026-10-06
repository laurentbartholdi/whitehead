import RequestProject.OrderUniversalDeckChains
import RequestProject.OrderUniversalChainNormalization
import RequestProject.PresUniversalRelatorDeck

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool))
  (hpos : ∀ j, 0 < (w j).length)

/-- Genuine finite relator coordinates of an actual path-class universal-cover chain. -/
noncomputable def presUniversalRelatorCoordinates :
    (UF (orderCx (PresPos w)) (ptBase w) →₀ ℤ) →ₗ[ℤ]
      (PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w)) →₀ ℤ) :=
  (presCoverRelatorChain w uOrderEnd (presUniversalEnd_isPosetCover w hpos) hpos).comp
    uOrderNormalizeChain2

/-- Equal actual relator coordinates detect equality of the normalized genuine cover cycles. -/
theorem presUniversalRelatorCoordinates_cycle_ext
    (c d : UF (orderCx (PresPos w)) (ptBase w) →₀ ℤ)
    (hc : Comb.bdry2 (uCover (orderCx (PresPos w)) (ptBase w)) c = 0)
    (hd : Comb.bdry2 (uCover (orderCx (PresPos w)) (ptBase w)) d = 0)
    (he : presUniversalRelatorCoordinates w hpos c =
      presUniversalRelatorCoordinates w hpos d) :
    uOrderNormalizeChain2 c = uOrderNormalizeChain2 d :=
  presCoverRelatorChain_cycle_injective w uOrderEnd (presUniversalEnd_isPosetCover w hpos)
    hpos _ _ (uOrderNormalizeChain2_cycle c hc) (uOrderNormalizeChain2_cycle d hd) he

/-- The coordinates recover the genuine relator chain on actual strict cover triangles. -/
theorem presUniversalRelatorCoordinates_inclusion
    (c : StrictOrdTri (UOrder (PresPos w) (ptBase w)) →₀ ℤ) :
    presUniversalRelatorCoordinates w hpos
      (chain2 uOrderHom (Finsupp.mapDomain (strictOrderIncl _).onF c)) =
      presCoverRelatorChain w uOrderEnd (presUniversalEnd_isPosetCover w hpos) hpos c := by
  change presCoverRelatorChain w uOrderEnd (presUniversalEnd_isPosetCover w hpos) hpos
    (uOrderNormalizeChain2 _) = _
  rw [uOrderNormalizeChain2_inclusion]

/-- The actual finite relator coordinates of path-class chains are deck equivariant. -/
theorem presUniversalRelatorCoordinates_deck
    (g : Pi1 (orderCx (PresPos w)) (ptBase w))
    (c : UF (orderCx (PresPos w)) (ptBase w) →₀ ℤ) :
    presUniversalRelatorCoordinates w hpos (Finsupp.mapDomain (deckF g) c) =
      Finsupp.mapDomain
        (presCoverRelatorMap w uOrderEnd uOrderEnd (uOrderDeckOrderIso g)
          (fun x => endV_deckV g x))
        (presUniversalRelatorCoordinates w hpos c) := by
  change presCoverRelatorChain w uOrderEnd (presUniversalEnd_isPosetCover w hpos) hpos
    (uOrderNormalizeChain2 (Finsupp.mapDomain (deckF g) c)) = _
  rw [uOrderNormalizeChain2_deck]
  exact presUniversalRelatorChain_deck w hpos g (uOrderNormalizeChain2 c)

end FiniteChains.PresModel
