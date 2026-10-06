module

public import RequestProject.RankOneCylinderRealization
public import RequestProject.PresPosetDimension

@[expose] public section

/-! The actual topological mapping cylinder in the presentation model
collapses to the subdivided rose. The outer attaching circles are sent
to the exact realization maps reading their prescribed words. -/

noncomputable section
namespace FiniteChains.PresModel
open Comb CategoryTheory
open scoped Topology

variable {A J : Type} (w : J → List (A × Bool))

def presCylinderRealizationHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (orderNerveRealization (CylBase w))
      (orderNerveRealization (Rose A)) :=
  rankOneCylinderRealizationHomotopyEquiv (aHom w) (circleDimension w)
    (circleDimension_strictMono w) (circleDimension_le_one w)

theorem presCylinderRealizationHomotopyEquiv_base :
    (presCylinderRealizationHomotopyEquiv w).toFun.comp
      (cylinderRealizationInclusion (aHom w)) = ContinuousMap.id _ :=
  cylinderRealization_section (aHom w)

theorem presCylinderRealizationHomotopyEquiv_outer :
    (presCylinderRealizationHomotopyEquiv w).toFun.comp
      (⟨orderNerveRealizationMap (cylOuter (aHom w)) (cylOuter_monotone (aHom w)),
        (orderNerveRealizationMap (cylOuter (aHom w))
          (cylOuter_monotone (aHom w))).hom.continuous⟩ :
          C(orderNerveRealization (TCirc w), orderNerveRealization (CylBase w))) =
      (⟨orderNerveRealizationMap (aFun w) (aFun_monotone w),
        (orderNerveRealizationMap (aFun w) (aFun_monotone w)).hom.continuous⟩ :
          C(orderNerveRealization (TCirc w), orderNerveRealization (Rose A))) := by
  apply ContinuousMap.ext
  intro x
  change orderNerveRealizationMap (cylRetr (aHom w)) (cylRetr_monotone (aHom w))
    (orderNerveRealizationMap (cylOuter (aHom w)) (cylOuter_monotone (aHom w)) x) = _
  rw [orderNerveRealizationMap_comp]
  rfl

end FiniteChains.PresModel
