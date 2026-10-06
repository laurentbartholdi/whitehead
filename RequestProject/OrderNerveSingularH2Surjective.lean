import RequestProject.OrderNerveSingularTwoCycles
import RequestProject.OrderNerveSingularHomologyComparison
import RequestProject.TopologicalSingular.HomologySurjectivity

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular

/-- The actual realization unit is surjective on second singular homology. -/
theorem orderNerveExplicitSingularH2_epi (P : Type) [PartialOrder P] :
    Epi (HomologicalComplex.homologyMap (orderNerveExplicitSingularMap P) 2) := by
  unfold HomologicalComplex.homologyMap HomologicalComplex.shortComplexFunctor
  apply shortComplex_homologyMap_epi_of_representatives
  intro c hc
  change Chain (orderNerveRealization P) 2 at c
  change ((complex (orderNerveRealization P)).d 2 ((ComplexShape.down ℕ).next 2)) c = 0 at hc
  rw (config := { transparency := .default }) [ChainComplex.next_nat_succ, complex_d] at hc
  obtain ⟨z, hz, b, hb⟩ := orderNerveRealization_twoCycle_cellularRepresentative c hc
  refine ⟨Finsupp.mapDomain (ordTriNerveEquiv P) z, ?_, ?_⟩
  · change (AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).d 2
      ((ComplexShape.down ℕ).next 2) _ = 0
    rw (config := { transparency := .default }) [ChainComplex.next_nat_succ, AlternatingFaceMapComplex.obj_d_eq]
    change (AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 1).hom
      (Finsupp.mapDomain (ordTriNerveEquiv P) z) = 0
    rw (config := { transparency := .default }) [mathlibOrderNerve_d2, hz, Finsupp.mapDomain_zero]
  · change ∃ a : (complex (orderNerveRealization P)).X ((ComplexShape.down ℕ).prev 2),
      (complex (orderNerveRealization P)).d ((ComplexShape.down ℕ).prev 2) 2 a = _
    rw (config := { transparency := .default }) [ChainComplex.prev]
    refine ⟨b, ?_⟩
    rw (config := { transparency := .default }) [complex_d]
    exact hb

theorem orderNerveSingularH2Comparison_factor (P : Type) [PartialOrder P] :
    orderNerveSingularH2Comparison P =
      HomologicalComplex.homologyMap (orderNerveExplicitSingularMap P) 2 ≫
        (homologyMathlibIso (orderNerveRealization P) 2).hom := by
  have he : orderNerveExplicitSingularMap P ≫ (complexMathlibIso (orderNerveRealization P)).hom =
      orderNerveRealizationChainComparison P ≫
        (FiniteChains.freeSingularChainComplexIso (orderNerveRealization P)).hom := by
    simp [orderNerveExplicitSingularMap, complexMathlibIso, Category.assoc]
  change (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 2).map
      (orderNerveRealizationChainComparison P) ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 2).map
        (FiniteChains.freeSingularChainComplexIso (orderNerveRealization P)).hom =
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 2).map
      (orderNerveExplicitSingularMap P) ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 2).map
        (complexMathlibIso (orderNerveRealization P)).hom
  rw (config := { transparency := .default }) [← Functor.map_comp, ← Functor.map_comp, he]

theorem orderNerveSingularH2Comparison_epi (P : Type) [PartialOrder P] :
    Epi (orderNerveSingularH2Comparison P) := by
  rw (config := { transparency := .default }) [orderNerveSingularH2Comparison_factor]
  letI := orderNerveExplicitSingularH2_epi P
  infer_instance

theorem orderCellSingularH2Map_surjective (P : Type) [PartialOrder P] :
    Function.Surjective (orderCellSingularH2Map P) := by
  intro x
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective _).mp (orderNerveSingularH2Comparison_epi P) x
  obtain ⟨z, rfl⟩ := (mathlibOrderNerveComplexH2Equiv P).surjective y
  exact ⟨z, hy⟩

/-- A zero cellular pushdown annihilates every actual singular second-homology
class, without any remaining comparison-image hypothesis. -/
theorem orderNerveSingularH2Map_zero_of_orderH2Map_zero {P Q : Type}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) (hf : Monotone f)
    (hzero : orderNerveH2Map f hf = 0) :
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
      (orderNerveRealizationMap f hf)) = 0 := by
  letI := orderNerveSingularH2Comparison_epi P
  apply (cancel_epi (orderNerveSingularH2Comparison P)).mp
  rw (config := { transparency := .default }) [orderNerveSingularH2Comparison_pushdown_zero f hf hzero, Limits.comp_zero]

end FiniteChains.Comb
