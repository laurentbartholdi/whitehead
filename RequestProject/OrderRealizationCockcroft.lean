import RequestProject.TopologicalPi1Lifting
import RequestProject.OrderRealizationHurewicz
import RequestProject.OrderUniversalRealizationCover

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology

theorem orderH2Map_zero_of_orderNerveSingularH2Map_zero {P Q : Type}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) (hf : Monotone f)
    (hz : (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
      (orderNerveRealizationMap f hf)) = 0) : orderNerveH2Map f hf = 0 := by
  apply LinearMap.ext
  intro z
  apply (orderCellSingularH2Equiv Q).injective
  rw [← orderCellSingularH2Equiv_natural f hf, hz]
  exact (orderCellSingularH2Equiv Q).map_zero.symm

/-- The cellular pushdown criterion is equivalent to the genuine topological
Cockcroft property, using the constructed simply connected covering. -/
theorem orderRealization_isCockcroft_iff {P : Type} [PartialOrder P]
    (a : P) (hc : IsConnected (orderCx P)) :
    Whitehead.IsCockcroft (orderNerveRealization P) ↔
      orderNerveH2Map (uOrderEnd : UOrder P a → P) uOrderEnd_monotone = 0 := by
  letI := uOrderRealization_simplyConnected a
  rw [Whitehead.isCockcroft_iff_cover_homology_zero
    (uOrderRealizationProjection a) (uOrderRealizationProjection_isCoveringMap a hc)
    (uOrderRealizationProjection_surjective a hc)]
  exact ⟨orderH2Map_zero_of_orderNerveSingularH2Map_zero _ _,
    orderNerveSingularH2Map_zero_of_orderH2Map_zero _ _⟩

/-- No existence-of-universal-cover assumption remains for order realizations. -/
theorem killsPi2_orderRealization_of_isCockcroft_of_killsPi1
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    {P : Type} [PartialOrder P] (a : P) (hc : IsConnected (orderCx P))
    (hX : Whitehead.IsCockcroft X) (f : C(X, orderNerveRealization P))
    (hf : Whitehead.KillsPi1 f) : Whitehead.KillsPi2 f := by
  letI := uOrderRealization_simplyConnected a
  exact Whitehead.killsPi2_of_isCockcroft_of_killsPi1 hX f hf
    (uOrderRealizationProjection a) (uOrderRealizationProjection_isCoveringMap a hc)
    (uOrderRealizationProjection_surjective a hc)

end FiniteChains.Comb
