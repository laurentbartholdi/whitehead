import RequestProject.GenusNonemptyWords
import RequestProject.PresentationQuotientCycleGeneration

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel
variable {α Jr : Type} (ρ : Jr ⊕ PUnit → FreeGroup α)
  (a b : ℕ → α) (q : ℕ) [NeZero q]

/-- Actual canonical generation for the connected genus presentation model. -/
theorem genusNonempty_quotient_cycle_generation
    (z : UF (orderCx (Qpos (cmpRel (SCell (gvc q) (gec q) (gc q))) (PresPos (genusNonemptyW ρ a b q)) (genusNonemptyAtt ρ a b q))) (qNew (A := cmpRel (SCell (gvc q) (gec q) (gc q))) (att := genusNonemptyAtt ρ a b q)
      (ptBase (genusNonemptyW ρ a b q))) →₀ ℤ)
    (hz : Comb.bdry2 (uCover (orderCx (Qpos (cmpRel (SCell (gvc q) (gec q) (gc q))) (PresPos (genusNonemptyW ρ a b q)) (genusNonemptyAtt ρ a b q))) (qNew (A := cmpRel (SCell (gvc q) (gec q) (gc q))) (att := genusNonemptyAtt ρ a b q)
      (ptBase (genusNonemptyW ρ a b q)))) z = 0) :
    ∃ (s : Finset (OrderComponent (QLiftedBase (qNew (A := cmpRel (SCell (gvc q) (gec q) (gc q))) (att := genusNonemptyAtt ρ a b q) (ptBase (genusNonemptyW ρ a b q))))))
      (g : OrderComponent (QLiftedBase (qNew (A := cmpRel (SCell (gvc q) (gec q) (gc q))) (att := genusNonemptyAtt ρ a b q) (ptBase (genusNonemptyW ρ a b q)))) →
        Pi1 (orderCx (Qpos (cmpRel (SCell (gvc q) (gec q) (gc q))) (PresPos (genusNonemptyW ρ a b q)) (genusNonemptyAtt ρ a b q))) (qNew (A := cmpRel (SCell (gvc q) (gec q) (gc q))) (att := genusNonemptyAtt ρ a b q)
      (ptBase (genusNonemptyW ρ a b q))))
      (d : OrderComponent (QLiftedBase (qNew (A := cmpRel (SCell (gvc q) (gec q) (gc q))) (att := genusNonemptyAtt ρ a b q) (ptBase (genusNonemptyW ρ a b q)))) →
        (UF (orderCx (PresPos (genusNonemptyW ρ a b q))) (ptBase (genusNonemptyW ρ a b q)) →₀ ℤ)),
      (∀ i, Comb.bdry2 (uCover (orderCx (PresPos (genusNonemptyW ρ a b q))) (ptBase (genusNonemptyW ρ a b q))) (d i) = 0) ∧
      ∃ y : UOrdTet (Qpos (cmpRel (SCell (gvc q) (gec q) (gc q))) (PresPos (genusNonemptyW ρ a b q)) (genusNonemptyAtt ρ a b q)) (qNew (A := cmpRel (SCell (gvc q) (gec q) (gc q))) (att := genusNonemptyAtt ρ a b q)
      (ptBase (genusNonemptyW ρ a b q))) →₀ ℤ,
        z = (∑ i ∈ s, Finsupp.mapDomain
          (deckF (g i) ∘ univLiftF (ptBase (genusNonemptyW ρ a b q))
            (orderCxMap (qNew (X := PresPos (genusNonemptyW ρ a b q)) (A := cmpRel (SCell (gvc q) (gec q) (gc q))) (att := genusNonemptyAtt ρ a b q)) qNew_monotone)) (d i)) +
          uOrdBoundary3 y := by
  exact presPos_quotient_cycle_generation (genusNonemptyW ρ a b q)
    (genusNonemptyW_ne_nil ρ a b q) (genusNonemptyAtt ρ a b q) z hz

end FiniteChains.Davis.Genus
