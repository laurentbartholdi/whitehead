import RequestProject.GenusCappedMathlibHomologyPushdown
import RequestProject.OrderNerveSingularHomologyComparison

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel CategoryTheory
variable {V : Type} [DecidableEq V] [Fintype V] {A : CommRel V}
variable (q : ℕ) [NeZero q]

/-- The concrete capped quotient projection induces zero on the actual full nerve
chain complex's second homology. -/
theorem cappedSpineQuotient_mathlib_complex_homology_pushdown_zero
    (w : SpinePresentationRel q ⊕ (Fin q × Bool) → List (SpinePresentationGen q × Bool))
    (hw : ∀ j, FreeGroup.mk (w j) = cappedSpinePresentation q j)
    (hpos : ∀ j, 0 < (w j).length)
    (att : NeSpx A →o PresPos w) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 2).map
      (mathlibOrderNerveChainMap
        (uOrderEnd : UOrder (Qpos A (PresPos w) att)
          (qNew (A := A) (att := att) (ptBase w)) → Qpos A (PresPos w) att)
        uOrderEnd_monotone) = 0 :=
  mathlibOrderNerveComplex_homologyMap_zero _ _
    (cappedSpineQuotient_homology_pushdown_map_zero q w hw hpos att)

/-- Singular-homology pushdown for the actual realized capped quotient projection
annihilates the image of the actual realization-unit comparison. -/
theorem cappedSpineQuotient_singular_comparison_pushdown_zero
    (w : SpinePresentationRel q ⊕ (Fin q × Bool) → List (SpinePresentationGen q × Bool))
    (hw : ∀ j, FreeGroup.mk (w j) = cappedSpinePresentation q j)
    (hpos : ∀ j, 0 < (w j).length)
    (att : NeSpx A →o PresPos w) :
    orderNerveSingularH2Comparison
        (UOrder (Qpos A (PresPos w) att) (qNew (A := A) (att := att) (ptBase w))) ≫
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
        (ModuleCat.of ℤ ℤ)).map (orderNerveRealizationMap
          (uOrderEnd : UOrder (Qpos A (PresPos w) att)
            (qNew (A := A) (att := att) (ptBase w)) → Qpos A (PresPos w) att)
          uOrderEnd_monotone)) = 0 :=
  orderNerveSingularH2Comparison_pushdown_zero _ _
    (cappedSpineQuotient_homology_pushdown_map_zero q w hw hpos att)

end FiniteChains.Davis.Genus
