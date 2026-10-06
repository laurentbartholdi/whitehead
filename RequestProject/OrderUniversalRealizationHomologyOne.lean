import RequestProject.OrderUniversalRealizationSimplyConnected
import RequestProject.TopologicalSingular.MathlibH1Comparison

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology

/-- The constructed universal order realization has zero actual singular H1. -/
theorem uOrderRealizationHomologyOne_isZero {P : Type} [PartialOrder P] (a : P) :
    Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization (UOrder P a))) := by
  letI : SimplyConnectedSpace (orderNerveRealization (UOrder P a)) :=
    uOrderRealization_simplyConnected a
  exact TopologicalSingular.mathlibHomologyOne_isZero_of_simplyConnected
    (orderNerveRealization (UOrder P a))

end FiniteChains.Comb
