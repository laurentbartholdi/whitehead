import RequestProject.OrderNerveRealizationStarContractible
import RequestProject.TopologicalSingular.MathlibComparison

namespace FiniteChains.Comb

/-- Actual closed vertex stars have zero integral singular homology in every
positive degree, in the exact sense used by Theorem A. -/
theorem orderNerveRealization_closedStar_acyclic {P : Type} [PartialOrder P] (v : P) :
    Whitehead.Acyclic (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v) :
      Set (orderNerveRealization P)) := by
  letI := orderNerveRealization_closedStar_contractible v
  exact Whitehead.acyclic_of_contractible _

/-- Actual open vertex stars are integrally acyclic in every positive degree. -/
theorem orderNerveRealizationOpenStar_acyclic {P : Type} [PartialOrder P] (v : P) :
    Whitehead.Acyclic (orderNerveRealizationOpenStar P v) := by
  letI := orderNerveRealizationOpenStar_contractible v
  exact Whitehead.acyclic_of_contractible _

end FiniteChains.Comb
