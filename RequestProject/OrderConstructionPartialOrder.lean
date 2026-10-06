import RequestProject.CylinderPoset
import RequestProject.ConeAdjPoset

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u

instance cylP_partialOrder {X S : Type u} [PartialOrder X] [PartialOrder S]
    (a : S →o X) : PartialOrder (CylP a) :=
  { (inferInstance : Preorder (CylP a)) with
    le_antisymm := by
      intro p q hpq hqp
      cases p <;> cases q
      · exact congrArg Sum.inl (le_antisymm hpq hqp)
      · exact False.elim hpq
      · exact False.elim hqp
      · exact congrArg Sum.inr (le_antisymm hpq hqp) }

instance coneAdj_partialOrder {P T : Type u} [PartialOrder P] (S : T → P → Prop) :
    PartialOrder (ConeAdj S) :=
  { (inferInstance : Preorder (ConeAdj S)) with
    le_antisymm := by
      intro p q hpq hqp
      cases p <;> cases q
      · exact congrArg Sum.inl (le_antisymm hpq hqp)
      · exact False.elim hqp
      · exact False.elim hpq
      · exact congrArg Sum.inr hpq }

end FiniteChains.Comb
