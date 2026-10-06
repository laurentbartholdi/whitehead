import RequestProject.GenusCappedSingularComparisonPushdown
import RequestProject.OrderNerveSingularH2Surjective

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel CategoryTheory
variable {V : Type} [DecidableEq V] [Fintype V] {A : CommRel V}
variable (q : ℕ) [NeZero q]

/-- The capped quotient projection annihilates all actual singular H2 classes.
The realization comparison is now proved surjective, so no image restriction remains. -/
theorem cappedSpineQuotient_singular_homology_pushdown_zero
    (w : SpinePresentationRel q ⊕ (Fin q × Bool) → List (SpinePresentationGen q × Bool))
    (hw : ∀ j, FreeGroup.mk (w j) = cappedSpinePresentation q j)
    (hpos : ∀ j, 0 < (w j).length)
    (att : NeSpx A →o PresPos w) :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).map (orderNerveRealizationMap
        (uOrderEnd : UOrder (Qpos A (PresPos w) att)
          (qNew (A := A) (att := att) (ptBase w)) → Qpos A (PresPos w) att)
        uOrderEnd_monotone)) = 0 :=
  orderNerveSingularH2Map_zero_of_orderH2Map_zero _ _
    (cappedSpineQuotient_homology_pushdown_map_zero q w hw hpos att)

end FiniteChains.Davis.Genus
