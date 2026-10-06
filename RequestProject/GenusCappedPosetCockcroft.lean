module

public import RequestProject.GenusCappedCockcroft
public import RequestProject.PresUniversalCockcroftCoordinates

@[expose] public section

namespace FiniteChains.Davis.Genus
open Comb PresModel
variable (q : ℕ) [NeZero q]

/-- Genuine order-poset universal two-cycles of the actual capped spine have zero base relator coefficients. -/
theorem cappedSpinePoset_relator_augmentation_zero
    (w : SpinePresentationRel q ⊕ (Fin q × Bool) → List (SpinePresentationGen q × Bool))
    (hw : ∀ j, FreeGroup.mk (w j) = cappedSpinePresentation q j)
    (hpos : ∀ j, 0 < (w j).length)
    (c : LinearMap.ker (Comb.bdry2 (strictOrderCx (UOrder (PresPos w) (ptBase w))))) :
    Finsupp.mapDomain (fun p => p.val.2)
      (presCoverRelatorChain w uOrderEnd (presUniversalEnd_isPosetCover w hpos) hpos c.val) = 0 := by
  classical
  letI : Fintype (SpinePresentationRel q ⊕ (Fin q × Bool)) := Fintype.ofFinite _
  exact presUniversalCockcroft_relator_augmentation_zero
    (cappedSpinePresentation q) w hw hpos (cappedSpinePresentation_isCockcroft q) c

/-- A concrete nonempty-word order-poset model of the actual capped-spine presentation. -/
noncomputable def cappedSpinePosetWords (a : SpinePresentationGen q) :=
  presNonemptyWords (cappedSpinePresentation q) a

theorem cappedSpinePosetWords_positive (a : SpinePresentationGen q) (j) :
    0 < (cappedSpinePosetWords q a j).length :=
  List.length_pos_iff.mpr (presNonemptyWords_ne_nil (cappedSpinePresentation q) a j)

/-- Zero augmentation for actual universal two-cycles in the concrete nonempty-word capped model. -/
theorem cappedSpineNonemptyPoset_relator_augmentation_zero (a : SpinePresentationGen q)
    (c : LinearMap.ker (Comb.bdry2 (strictOrderCx
      (UOrder (PresPos (cappedSpinePosetWords q a)) (ptBase (cappedSpinePosetWords q a)))))) :
    Finsupp.mapDomain (fun p => p.val.2)
      (presCoverRelatorChain (cappedSpinePosetWords q a) uOrderEnd
        (presUniversalEnd_isPosetCover _ (cappedSpinePosetWords_positive q a))
        (cappedSpinePosetWords_positive q a) c.val) = 0 :=
  cappedSpinePoset_relator_augmentation_zero q _
    (mk_presNonemptyWords (cappedSpinePresentation q) a)
    (cappedSpinePosetWords_positive q a) c

end FiniteChains.Davis.Genus
