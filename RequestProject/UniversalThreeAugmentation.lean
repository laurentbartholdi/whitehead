import RequestProject.OrderUniversalThree
import RequestProject.CombPi2

/-! Forgetting the deck coordinate of the actual lifted three-boundary. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] (a : P)

theorem hurewicz_uOrdTetBoundary (t : UOrdTet P a) :
    hurewicz (orderCx P) a (uOrdTetBoundary t) = ordTetBoundary t.1.2 := by
  have hs (c d : UF (orderCx P) a →₀ ℤ) :
      Finsupp.mapDomain (univProj (orderCx P) a).onF (c - d) =
        Finsupp.mapDomain (univProj (orderCx P) a).onF c -
          Finsupp.mapDomain (univProj (orderCx P) a).onF d :=
    (Finsupp.lmapDomain ℤ ℤ (univProj (orderCx P) a).onF).map_sub c d
  change Finsupp.mapDomain (univProj (orderCx P) a).onF (uOrdTetBoundary t) = _
  simp only [uOrdTetBoundary, hs, Finsupp.mapDomain_add, Finsupp.mapDomain_single]
  rfl

/-- Augmentation commutes with the actual degree-three cellular boundary. -/
theorem hurewicz_uOrdBoundary3 (c : UOrdTet P a →₀ ℤ) :
    hurewicz (orderCx P) a (uOrdBoundary3 c) =
      ordBoundary3 (Finsupp.mapDomain (fun t : UOrdTet P a => t.1.2) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, Finsupp.mapDomain_add, map_add]
  | single t n =>
      rw [uOrdBoundary3, Finsupp.linearCombination_single, map_smul,
        hurewicz_uOrdTetBoundary, Finsupp.mapDomain_single, ordBoundary3,
        Finsupp.linearCombination_single]

end FiniteChains.Comb
