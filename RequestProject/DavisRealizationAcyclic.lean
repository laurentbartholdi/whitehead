module

public import RequestProject.OrderNerveSingularAcyclicity
public import RequestProject.DavisChainAcyclic

@[expose] public section

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [Fintype V]

/-- All positive integral singular homology groups of the actual Davis realization vanish. -/
theorem davisRealization_acyclic (A : CommRel V) :
    Whitehead.Acyclic (orderNerveRealization (Sph A)) :=
  orderNerveRealization_acyclic_of_nerve
    (fun _ hz hcycle => exists_bdry_eq_of_cycle_davis A hz hcycle)

end FiniteChains.Davis
