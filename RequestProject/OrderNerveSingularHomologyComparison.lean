import RequestProject.OrderNerveRealizationComparison
import RequestProject.FreeSingularChainComparison
import RequestProject.MathlibOrderNerveComplexNaturality

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory

/-- The realization unit induces an actual map to Mathlib integral singular homology.
This definition makes no claim that the map is an isomorphism. -/
noncomputable def orderNerveSingularH2Comparison (P : Type) [PartialOrder P] :
    (AlgebraicTopology.AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).homology 2 ⟶
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)) :=
  orderNerveRealizationH2Comparison P ≫
    (FiniteChains.freeSingularHomologyIso (orderNerveRealization P) 2).hom

/-- The actual singular-homology comparison is natural for monotone maps. -/
theorem orderNerveSingularH2Comparison_natural {P Q : Type}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) (hf : Monotone f) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 2).map
      (mathlibOrderNerveChainMap f hf) ≫ orderNerveSingularH2Comparison Q =
    orderNerveSingularH2Comparison P ≫
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)).map (orderNerveRealizationMap f hf)) := by
  unfold orderNerveSingularH2Comparison
  rw [← Category.assoc, orderNerveRealizationH2Comparison_natural, Category.assoc]
  change _ ≫ ((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 2).map
      (AlgebraicTopology.AlternatingFaceMapComplex.map
        (Functor.whiskerRight (TopCat.toSSet.map (orderNerveRealizationMap f hf))
          (ModuleCat.free ℤ))) ≫ _) = _
  rw [FiniteChains.freeSingularHomologyIso_natural, Category.assoc]

/-- A zero order-homology pushdown annihilates all singular classes in the comparison image. -/
theorem orderNerveSingularH2Comparison_pushdown_zero {P Q : Type}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) (hf : Monotone f)
    (hzero : orderNerveH2Map f hf = 0) :
    orderNerveSingularH2Comparison P ≫
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)).map (orderNerveRealizationMap f hf)) = 0 := by
  rw [← orderNerveSingularH2Comparison_natural,
    mathlibOrderNerveComplex_homologyMap_zero f hf hzero]
  exact CategoryTheory.Limits.zero_comp

/-- The actual order-cell second-homology classes map to genuine singular classes. -/
noncomputable def orderCellSingularH2Map (P : Type) [PartialOrder P] :
    OrderNerveH2 P →ₗ[ℤ]
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)) :=
  (orderNerveSingularH2Comparison P).hom.comp
    (mathlibOrderNerveComplexH2Equiv P).toLinearMap

/-- Naturality of the comparison from actual order-cell classes to singular classes. -/
theorem orderCellSingularH2Map_natural {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) (z : OrderNerveH2 P) :
    ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).map (orderNerveRealizationMap f hf)).hom
        (orderCellSingularH2Map P z)) = orderCellSingularH2Map Q (orderNerveH2Map f hf z) := by
  have h := congrArg (fun k :
      (AlgebraicTopology.AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).homology 2 ⟶
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
          (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization Q)) =>
      k (mathlibOrderNerveComplexH2Equiv P z))
    (orderNerveSingularH2Comparison_natural f hf)
  change (orderNerveSingularH2Comparison Q).hom
      (((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 2).map
        (mathlibOrderNerveChainMap f hf)).hom (mathlibOrderNerveComplexH2Equiv P z)) =
    ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).map (orderNerveRealizationMap f hf)).hom
        (orderCellSingularH2Map P z)) at h
  rw [mathlibOrderNerveComplexH2Equiv_natural] at h
  exact h.symm

end FiniteChains.Comb
