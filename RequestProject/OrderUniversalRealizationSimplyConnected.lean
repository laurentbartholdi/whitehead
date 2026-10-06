module

public import RequestProject.OrderNerveRealizationSimplyConnected
public import RequestProject.OrderUniversalPosetConnected

@[expose] public section

namespace FiniteChains.Comb

/-- The actual realization of the path-class universal order is topologically
simply connected, without any connectedness assumption on the base poset. -/
theorem uOrderRealization_simplyConnected {P : Type} [PartialOrder P] (a : P) :
    SimplyConnectedSpace (orderNerveRealization (UOrder P a)) := by
  letI : Nonempty (UOrder P a) := ⟨UV.base (orderCx P) a⟩
  exact orderNerveRealization_simplyConnected (UOrder P a)
    uOrder_complex_isConnected uOrder_complex_simplyConnected

end FiniteChains.Comb
