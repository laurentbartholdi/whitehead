module

public import RequestProject.TopologicalSingular.HurewiczInjectivity
public import RequestProject.TopologicalSingular.HomologyToPi2

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular
open CategoryTheory AlgebraicTopology
variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem singularHurewicz2_bijective (x : X) : Function.Bijective (singularHurewicz2 x) :=
  ⟨singularHurewicz2_injective x, singularHurewicz2_surjective x⟩

/-- The genuine simply connected degree-two Hurewicz isomorphism. -/
noncomputable def singularHurewicz2MulEquiv (x : X) :
    HomotopyGroup (Fin 2) X x ≃*
      Multiplicative
        (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)) :=
  MulEquiv.ofBijective (singularHurewicz2Hom x)
    ⟨singularHurewicz2Hom_injective x, singularHurewicz2Hom_surjective x⟩

@[simp] theorem singularHurewicz2MulEquiv_apply (x : X) (q : HomotopyGroup (Fin 2) X x) :
    singularHurewicz2MulEquiv x q = Multiplicative.ofAdd (singularHurewicz2 x q) := rfl

noncomputable def singularHurewicz2Linear (x : X) :
    Additive (HomotopyGroup (Fin 2) X x) →ₗ[ℤ]
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)) :=
  (homologyMathlibIso (TopCat.of X) 2).hom.hom.comp (pi2CycleClassLinear x)

noncomputable def singularHurewicz2LinearEquiv (x : X) :
    Additive (HomotopyGroup (Fin 2) X x) ≃ₗ[ℤ]
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)) :=
  LinearEquiv.ofBijective (singularHurewicz2Linear x) ⟨by
    intro a b h
    exact congrArg Additive.ofMul (singularHurewicz2_injective x h), by
    intro q
    obtain ⟨p, hp⟩ := singularHurewicz2_surjective x q
    exact ⟨Additive.ofMul p, hp⟩⟩

@[simp] theorem singularHurewicz2LinearEquiv_apply (x : X)
    (q : Additive (HomotopyGroup (Fin 2) X x)) :
    singularHurewicz2LinearEquiv x q = singularHurewicz2 x q.toMul := rfl

/-- The previously constructed homology-to-pi2 map is also a left inverse,
now that injectivity has been established geometrically. -/
theorem singularH2ToPi2_pi2CycleClass (x : X) (q : Additive (HomotopyGroup (Fin 2) X x)) :
    singularH2ToPi2 x (pi2CycleClass x q.toMul) = q := by
  have h := pi2CycleClass_injective x
    (pi2CycleClass_singularH2ToPi2 x (pi2CycleClass x q.toMul))
  exact congrArg Additive.ofMul h

theorem singularH2ToPi2Linear_comp_pi2CycleClassLinear (x : X) :
    (singularH2ToPi2Linear x).comp (pi2CycleClassLinear x) = LinearMap.id := by
  ext q
  exact singularH2ToPi2_pi2CycleClass x q

end FiniteChains.TopologicalSingular
