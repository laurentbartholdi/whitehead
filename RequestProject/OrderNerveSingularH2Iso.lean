import RequestProject.OrderNerveSingularBoundaryReflection
import RequestProject.OrderNerveSingularH2Surjective
import RequestProject.TopologicalSingular.HomologyInjectivity

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular

/-- The canonical realization comparison is injective on every positive
singular homology group. -/
theorem orderNerveExplicitSingularHomology_mono (P : Type) [PartialOrder P] (n : ℕ) :
    Mono (HomologicalComplex.homologyMap (orderNerveExplicitSingularMap P) (n + 1)) := by
  unfold HomologicalComplex.homologyMap HomologicalComplex.shortComplexFunctor
  apply shortComplex_homologyMap_mono_of_reflects_boundaries
  intro c hc hb
  change ComposableArrows P (n + 1) →₀ ℤ at c
  change (AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).d (n + 1)
    ((ComplexShape.down ℕ).next (n + 1)) c = 0 at hc
  rw [ChainComplex.next_nat_succ, AlternatingFaceMapComplex.obj_d_eq] at hc
  change ∃ b : (complex (orderNerveRealization P)).X ((ComplexShape.down ℕ).prev (n + 1)),
    (complex (orderNerveRealization P)).d ((ComplexShape.down ℕ).prev (n + 1)) (n + 1) b = _ at hb
  rw [ChainComplex.prev] at hb
  obtain ⟨b, hb⟩ := hb
  rw [complex_d] at hb
  obtain ⟨a, ha⟩ := orderNerveExplicitSingular_reflects_boundaries n c hc b hb
  change ∃ a : (AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).X
    ((ComplexShape.down ℕ).prev (n + 1)),
    (AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).d
      ((ComplexShape.down ℕ).prev (n + 1)) (n + 1) a = c
  rw [ChainComplex.prev]
  refine ⟨a, ?_⟩
  rw [AlternatingFaceMapComplex.obj_d_eq]
  exact ha

theorem orderNerveSingularH2Comparison_mono (P : Type) [PartialOrder P] :
    Mono (orderNerveSingularH2Comparison P) := by
  rw [orderNerveSingularH2Comparison_factor]
  letI := orderNerveExplicitSingularHomology_mono P 1
  infer_instance

theorem orderNerveSingularH2Comparison_isIso (P : Type) [PartialOrder P] :
    IsIso (orderNerveSingularH2Comparison P) := by
  letI := orderNerveSingularH2Comparison_mono P
  letI := orderNerveSingularH2Comparison_epi P
  exact isIso_of_mono_of_epi _

theorem orderCellSingularH2Map_injective (P : Type) [PartialOrder P] :
    Function.Injective (orderCellSingularH2Map P) := by
  have h := (ModuleCat.mono_iff_injective _).mp (orderNerveSingularH2Comparison_mono P)
  exact h.comp (mathlibOrderNerveComplexH2Equiv P).injective

/-- An actual isomorphism, with the original natural comparison as forward map. -/
noncomputable def orderCellSingularH2Equiv (P : Type) [PartialOrder P] :
    OrderNerveH2 P ≃ₗ[ℤ]
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
        (orderNerveRealization P)) :=
  LinearEquiv.ofBijective (orderCellSingularH2Map P)
    ⟨orderCellSingularH2Map_injective P, orderCellSingularH2Map_surjective P⟩

theorem orderCellSingularH2Equiv_natural {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) (z : OrderNerveH2 P) :
    ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
      (orderNerveRealizationMap f hf)).hom (orderCellSingularH2Equiv P z)) =
        orderCellSingularH2Equiv Q (orderNerveH2Map f hf z) :=
  orderCellSingularH2Map_natural f hf z

end FiniteChains.Comb
