import RequestProject.CylinderCoverCollapsedCircle

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool)) (j : J)
  (f : P → CylBase w) (hf : IsPosetCover f) (m : RelatorCircle w j → P)
  (hm : StrictMono m) (hp : ∀ x, f (m x) = cylOuter (aHom w) x.val)

/-- The actual collapsed midpoint associated to a valid letter of the lifted attaching circle. -/
noncomputable def cylinderCoverCollapsedLetterMidpoint (k : Fin (w j).length) :=
  roseCoverLetterMidpoint w j (cylinderCoverRoseEnd w f)
    (cylinderCoverCollapsedCircle w j f hf m)
    (cylinderCoverCollapsedCircle_projection w j f hf m hp) k ((w j)[k.val])
      (List.getElem?_eq_getElem k.isLt)

/-- Actual collapsed attaching coefficients are the signed sum of actual lifted letter incidences. -/
theorem cylinderCoverCollapsedCircle_coordinates :
    cylinderCoverCollapsedGeneratorCoordinates w f hf
      (chain1 (strictOrderCxMap m hm) (relatorCircleFundamentalChain w j)) =
      ∑ k : Fin (w j).length,
        (if ((w j)[k.val]).2 then (1 : ℤ) else -1) •
          Finsupp.single (roseCoverMidpointEdge (cylinderCoverRoseEnd w f)
            (cylinderCoverRoseEnd_isPosetCover w f hf)
            (cylinderCoverCollapsedLetterMidpoint w j f hf m hp k)) 1 := by
  classical
  change roseCoverGeneratorCoordinates (cylinderCoverRoseEnd w f)
    (cylinderCoverRoseEnd_isPosetCover w f hf)
      (cylinderCoverCollapsedRoseChain w f hf
        (chain1 (strictOrderCxMap m hm) (relatorCircleFundamentalChain w j))) = _
  rw [cylinderCoverCollapsedCircle_chain w j f hf m hm hp]
  exact roseCoverFundamentalChain_coordinates w j (cylinderCoverRoseEnd w f)
    (cylinderCoverRoseEnd_isPosetCover w f hf) (cylinderCoverCollapsedCircle w j f hf m)
    (cylinderCoverCollapsedCircle_strictMono w j f hf m hm hp)
    (cylinderCoverCollapsedCircle_projection w j f hf m hp)

end FiniteChains.PresModel
