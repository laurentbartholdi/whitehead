import RequestProject.Statement
import RequestProject.OrderNerveRealizationPaths

namespace FiniteChains.Comb
open CategoryTheory Topology

/-- The actual realized poset nerve, with its proved topology, CW structure,
connectedness and dimension, is a genuine two-complex of the submission statement. -/
noncomputable def orderNerveTwoComplex (P : Type) [PartialOrder P] [Nonempty P]
    [(nerve P).HasDimensionLE 2] (hP : IsConnected (orderCx P)) : Whitehead.TwoComplex := by
  letI : PathConnectedSpace (orderNerveRealization P) := orderNerveRealization_pathConnectedSpace P hP
  exact
    { space := orderNerveRealization P
      topology := inferInstance
      hausdorff := inferInstance
      cw := inferInstance
      connected := inferInstance
      dimension := fun n hn => orderNerveRealization_cell_isEmpty P 2 n hn }

end FiniteChains.Comb
