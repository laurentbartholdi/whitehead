import RequestProject.OrderStrictHomologyVanishing
import RequestProject.ConnectedCellularZeroFillings

namespace FiniteChains.Comb
open CategoryTheory
variable (P : Type) [PartialOrder P] [Nonempty P] [(nerve P).HasDimensionLE 2]

/-- Exact comparison of actual singular acyclicity and the strict cellular
acyclicity predicate, for every connected two-dimensional order realization. -/
theorem orderRealization_acyclic_iff_strict_isAcyclic (hP : IsConnected (orderCx P)) :
    Whitehead.Acyclic (orderNerveRealization P) ↔ IsAcyclic (strictOrderCx P) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · apply (injective_iff_map_eq_zero (bdry2 (strictOrderCx P))).mpr
      exact strict_twoCycle_eq_zero_of_singular_homology_zero (h 2 (by decide))
    · exact orderRealization_homology_one_isZero_iff_strict_fillings.mp (h 1 (by decide))
    · exact strict_order_zeroCycle_filling_of_connected (P := P)
        (Classical.choice ‹Nonempty P›) hP
  · exact orderRealization_acyclic_of_strict_isAcyclic

end FiniteChains.Comb
