import RequestProject.PresValidRealization
import RequestProject.TopologicalDeformationPi2

namespace FiniteChains.PresModel
open Comb
variable {α J : Type} (w : J → List (α × Bool))

/-- Removing the unused positions preserves actual pi2, via the actual
cell-preserving inclusion of the finite valid-position model. -/
noncomputable def presValidRealizationPi2Equiv (x : orderNerveRealization (ValidPresPos w)) :
    HomotopyGroup (Fin 2) (orderNerveRealization (ValidPresPos w)) x ≃*
      HomotopyGroup (Fin 2) (orderNerveRealization (PresPos w))
        (presValidRealizationInclusion w x) :=
  Whitehead.pi2DeformationRetractEquiv
    (presValidRealizationInclusion w) (presValidRealizationRetraction w)
    (presValidRealization_section w) (presValidRealizationDeformation w)
    (presValidRealizationDeformation_fixed w) x

theorem presValidRealizationPi2Equiv_apply (x : orderNerveRealization (ValidPresPos w))
    (q : HomotopyGroup (Fin 2) (orderNerveRealization (ValidPresPos w)) x) :
    presValidRealizationPi2Equiv w x q = Whitehead.pi2Map (presValidRealizationInclusion w) x q :=
  rfl

end FiniteChains.PresModel
