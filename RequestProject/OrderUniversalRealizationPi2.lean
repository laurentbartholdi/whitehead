module

public import RequestProject.OrderUniversalRealizationCover
public import RequestProject.OrderNerveCoverDimension
public import RequestProject.TopologicalCoverPi2

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory Topology

/-- Actual poset covering projections induce isomorphisms on the actual
Mathlib topological second homotopy groups. -/
noncomputable def posetCoverRealizationPi2Equiv {P Q : Type}
    [PartialOrder P] [PartialOrder Q] {f : P → Q}
    (hf : IsPosetCover f) (e : orderNerveRealization P) :
    HomotopyGroup (Fin 2) (orderNerveRealization P) e ≃*
      HomotopyGroup (Fin 2) (orderNerveRealization Q)
        (orderNerveRealizationMap f hf.mono e) :=
  Whitehead.pi2CoverEquiv
    ⟨orderNerveRealizationMap f hf.mono,
      (orderNerveRealizationMap f hf.mono).hom.continuous⟩
    hf.realizationMap_isCoveringMap e

variable {P : Type} [PartialOrder P] (a : P)

/-- The constructed path-class cover, now on genuine topological pi2. -/
noncomputable def uOrderRealizationPi2Equiv (hc : IsConnected (orderCx P))
    (e : orderNerveRealization (UOrder P a)) :
    HomotopyGroup (Fin 2) (orderNerveRealization (UOrder P a)) e ≃*
      HomotopyGroup (Fin 2) (orderNerveRealization P) (uOrderRealizationProjection a e) :=
  posetCoverRealizationPi2Equiv (uOrderEnd_isPosetCover (a := a) hc) e

/-- The constructed connected covering space is itself a genuine two-complex
when the base nerve is two-dimensional. -/
noncomputable def uOrderRealizationTwoComplex [(nerve P).HasDimensionLE 2]
    (hc : IsConnected (orderCx P)) : Whitehead.TwoComplex := by
  letI : (nerve (UOrder P a)).HasDimensionLE 2 :=
    (uOrderEnd_isPosetCover (a := a) hc).realization_hasDimensionLE 2
  letI : PathConnectedSpace (orderNerveRealization (UOrder P a)) :=
    uOrderRealization_pathConnectedSpace a
  exact
    { space := orderNerveRealization (UOrder P a)
      topology := inferInstance
      hausdorff := inferInstance
      cw := inferInstance
      connected := inferInstance
      dimension := fun n hn => orderNerveRealization_cell_isEmpty (UOrder P a) 2 n hn }

/-- Precomposition with the constructed endpoint covering reflects pi2-killing. -/
theorem killsPi2_uOrderRealization_precomp_iff (hc : IsConnected (orderCx P))
    {Y : Type} [TopologicalSpace Y] (g : C(orderNerveRealization P, Y)) :
    Whitehead.KillsPi2 (g.comp (uOrderRealizationProjection a)) ↔ Whitehead.KillsPi2 g :=
  Whitehead.killsPi2_covering_precomp_iff (uOrderRealizationProjection a)
    (uOrderRealizationProjection_isCoveringMap a hc)
    (uOrderRealizationProjection_surjective a hc) g

end FiniteChains.Comb
