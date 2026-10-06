import RequestProject.OrderNerveSingularH2Iso
import RequestProject.OrderNerveSingularAcyclicity

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular

theorem orderNerveExplicitSingularHomology_epi (P : Type) [PartialOrder P] (n : ℕ) :
    Epi (HomologicalComplex.homologyMap (orderNerveExplicitSingularMap P) (n + 1)) := by
  unfold HomologicalComplex.homologyMap HomologicalComplex.shortComplexFunctor
  apply shortComplex_homologyMap_epi_of_representatives
  intro c hc
  change Chain (orderNerveRealization P) (n + 1) at c
  change (complex (orderNerveRealization P)).d (n + 1)
    ((ComplexShape.down ℕ).next (n + 1)) c = 0 at hc
  rw (config := { transparency := .default }) [ChainComplex.next_nat_succ, complex_d] at hc
  obtain ⟨z, hz, _, hz0, b, hb⟩ := orderNerveRealization_cycle_nerveRepresentative n c hc
  refine ⟨orderNerveGradedDecode (n + 1) z, ?_, ?_⟩
  · change (AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).d (n + 1)
      ((ComplexShape.down ℕ).next (n + 1)) _ = 0
    rw (config := { transparency := .default }) [ChainComplex.next_nat_succ, AlternatingFaceMapComplex.obj_d_eq]
    change (AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) n).hom
      (orderNerveGradedDecode (n + 1) z) = 0
    apply orderNerveGradedEncode_injective n
    rw (config := { transparency := .default }) [orderNerveGradedEncode_boundary, orderNerveGradedEncode_decode _ hz,
      ← Nerve.lengthProjection_bdry, hz0, map_zero]
  · change ∃ a : (complex (orderNerveRealization P)).X ((ComplexShape.down ℕ).prev (n + 1)),
      (complex (orderNerveRealization P)).d ((ComplexShape.down ℕ).prev (n + 1)) (n + 1) a = _
    rw (config := { transparency := .default }) [ChainComplex.prev]
    refine ⟨b, ?_⟩
    rw (config := { transparency := .default }) [complex_d]
    exact hb

/-- The canonical realized-simplex map computes the actual positive integral
singular homology of every order-nerve realization, without finiteness assumptions. -/
theorem orderNerveExplicitSingularHomology_isIso (P : Type) [PartialOrder P] (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (orderNerveExplicitSingularMap P) (n + 1)) := by
  letI := orderNerveExplicitSingularHomology_mono P n
  letI := orderNerveExplicitSingularHomology_epi P n
  exact isIso_of_mono_of_epi _

noncomputable def orderNervePositiveSingularHomologyIso (P : Type) [PartialOrder P] (n : ℕ) :
    (AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).homology (n + 1) ≅
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj (ModuleCat.of ℤ ℤ)).obj
        (orderNerveRealization P)) := by
  letI := orderNerveExplicitSingularHomology_isIso P n
  exact asIso (HomologicalComplex.homologyMap (orderNerveExplicitSingularMap P) (n + 1)) ≪≫
    homologyMathlibIso (orderNerveRealization P) (n + 1)

end FiniteChains.Comb
