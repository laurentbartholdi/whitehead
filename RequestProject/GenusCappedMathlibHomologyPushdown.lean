import RequestProject.GenusCappedQuotientPushdown
import RequestProject.MathlibOrderNerveCategoricalNaturality

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel
variable {V : Type} [DecidableEq V] [Fintype V] {A : CommRel V}
variable (q : ℕ) [NeZero q]

/-- The actual capped-spine quotient extension has zero pushdown on Mathlib's
categorical second homology of its genuine alternating-face differential segment. -/
theorem cappedSpineQuotient_mathlib_homology_pushdown_zero
    (w : SpinePresentationRel q ⊕ (Fin q × Bool) → List (SpinePresentationGen q × Bool))
    (hw : ∀ j, FreeGroup.mk (w j) = cappedSpinePresentation q j)
    (hpos : ∀ j, 0 < (w j).length)
    (att : NeSpx A →o PresPos w) :
    CategoryTheory.ShortComplex.homologyMap (mathlibOrderNerveShortComplexMap
      (uOrderEnd : UOrder (Qpos A (PresPos w) att)
        (qNew (A := A) (att := att) (ptBase w)) → Qpos A (PresPos w) att)
      uOrderEnd_monotone) = 0 :=
  mathlibOrderNerve_homologyMap_zero _ _
    (cappedSpineQuotient_homology_pushdown_map_zero q w hw hpos att)

end FiniteChains.Davis.Genus
