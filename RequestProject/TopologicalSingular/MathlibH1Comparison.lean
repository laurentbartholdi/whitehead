import RequestProject.TopologicalSingular.SingularChainH1
import RequestProject.TopologicalSingular.MathlibComparison

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular
open CategoryTheory AlgebraicTopology

/-- Explicit path triangles and prisms give exactness in degree one for every
simply connected space. No Hurewicz assumption is introduced. -/
theorem simplyConnected_complex_exact_one {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] : (complex X).ExactAt 1 := by
  rw [HomologicalComplex.exactAt_iff' (K := complex X) (i := 2) (j := 1) (k := 0)
    (ChainComplex.prev ℕ 1) (ChainComplex.next_nat_succ 0)]
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  change LinearMap.range (((complex X).d 2 1).hom) =
    LinearMap.ker (((complex X).d 1 0).hom)
  rw [complex_d, complex_d]
  exact ker_boundary_zero_eq_range_one.symm

/-- Actual integral singular H1 vanishes for simply connected spaces. -/
theorem mathlibHomologyOne_isZero_of_simplyConnected (X : Type)
    [TopologicalSpace X] [SimplyConnectedSpace X] :
    Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)) :=
  (simplyConnected_complex_exact_one (X := X)).isZero_homology.of_iso
    (homologyMathlibIso (TopCat.of X) 1).symm

end FiniteChains.TopologicalSingular
