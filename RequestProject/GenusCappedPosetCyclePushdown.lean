import RequestProject.OrderNerveH2Maps
import RequestProject.GenusCappedPosetCockcroft
import RequestProject.PresCoverCyclePushdownZero
import RequestProject.PresUniversalCockcroftWeakPushdown
import RequestProject.OrderUniversalChainProjection

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open Comb PresModel
variable (q : ℕ) [NeZero q]

/-- Every genuine universal-cover two-cycle of the actual capped-spine order model
pushes to the zero triangle chain in the base. -/
theorem cappedSpinePoset_cycle_pushdown_zero
    (w : SpinePresentationRel q ⊕ (Fin q × Bool) → List (SpinePresentationGen q × Bool))
    (hw : ∀ j, FreeGroup.mk (w j) = cappedSpinePresentation q j)
    (hpos : ∀ j, 0 < (w j).length)
    (c : LinearMap.ker (Comb.bdry2 (strictOrderCx (UOrder (PresPos w) (ptBase w))))) :
    chain2 (strictOrderCxMap uOrderEnd (presUniversalEnd_isPosetCover w hpos).strictMono)
      c.val = 0 :=
  presCover_cycle_pushdown_zero w uOrderEnd (presUniversalEnd_isPosetCover w hpos) hpos
    c.val c.property (cappedSpinePoset_relator_augmentation_zero q w hw hpos c)

/-- The concrete nonempty-word capped-spine model has actual zero universal-cycle pushdown. -/
theorem cappedSpineNonemptyPoset_cycle_pushdown_zero (a : SpinePresentationGen q)
    (c : LinearMap.ker (Comb.bdry2 (strictOrderCx
      (UOrder (PresPos (cappedSpinePosetWords q a)) (ptBase (cappedSpinePosetWords q a)))))) :
    chain2 (strictOrderCxMap uOrderEnd
      (presUniversalEnd_isPosetCover _ (cappedSpinePosetWords_positive q a)).strictMono)
      c.val = 0 :=
  cappedSpinePoset_cycle_pushdown_zero q _
    (mk_presNonemptyWords (cappedSpinePresentation q) a)
    (cappedSpinePosetWords_positive q a) c

/-- Every actual weak universal two-cycle of the capped-spine order model
has an explicit three-filling after projection to the base order nerve. -/
theorem cappedSpinePoset_weak_cycle_pushdown_boundary
    (w : SpinePresentationRel q ⊕ (Fin q × Bool) → List (SpinePresentationGen q × Bool))
    (hw : ∀ j, FreeGroup.mk (w j) = cappedSpinePresentation q j)
    (hpos : ∀ j, 0 < (w j).length)
    (c : OrdTri (UOrder (PresPos w) (ptBase w)) →₀ ℤ)
    (hc : Comb.bdry2 (orderCx (UOrder (PresPos w) (ptBase w))) c = 0) :
    chain2 (orderCxMap uOrderEnd (presUniversalEnd_isPosetCover w hpos).mono) c =
      ordBoundary3 (ordNormalizationHomotopy2
        (chain2 (orderCxMap uOrderEnd (presUniversalEnd_isPosetCover w hpos).mono) c)) := by
  classical
  letI : Fintype (SpinePresentationRel q ⊕ (Fin q × Bool)) := Fintype.ofFinite _
  exact presUniversalCockcroft_weak_pushdown_boundary (cappedSpinePresentation q) w hw hpos
    (cappedSpinePresentation_isCockcroft q) c hc

/-- The original path-class universal-cover cycle pushdown has an explicit three-filling
for the genuine capped-spine presentation order model. -/
theorem cappedSpinePoset_path_cover_pushdown_boundary
    (w : SpinePresentationRel q ⊕ (Fin q × Bool) → List (SpinePresentationGen q × Bool))
    (hw : ∀ j, FreeGroup.mk (w j) = cappedSpinePresentation q j)
    (hpos : ∀ j, 0 < (w j).length)
    (c : UF (orderCx (PresPos w)) (ptBase w) →₀ ℤ)
    (hc : Comb.bdry2 (uCover (orderCx (PresPos w)) (ptBase w)) c = 0) :
    chain2 (univProj (X := orderCx (PresPos w)) (x₀ := ptBase w)) c =
      ordBoundary3 (ordNormalizationHomotopy2
        (chain2 (univProj (X := orderCx (PresPos w)) (x₀ := ptBase w)) c)) := by
  let r := uOrderChain2Equiv.symm c
  have hr : Comb.bdry2 (orderCx (UOrder (PresPos w) (ptBase w))) r = 0 := by
    apply (uOrderHom_cycle_iff r).mp
    change Comb.bdry2 (uCover (orderCx (PresPos w)) (ptBase w))
      (uOrderChain2Equiv (uOrderChain2Equiv.symm c)) = 0
    rw (config := { transparency := .default }) [uOrderChain2Equiv.apply_symm_apply]
    exact hc
  have hp := uOrderChain2Equiv_projection r
  rw (config := { transparency := .default }) [uOrderChain2Equiv.apply_symm_apply] at hp
  rw (config := { transparency := .default }) [hp]
  exact cappedSpinePoset_weak_cycle_pushdown_boundary q w hw hpos r hr

/-- Actual capped-spine universal-cover cycles push to zero in the second
integral homology of the base order nerve. -/
theorem cappedSpinePoset_path_cover_pushdown_homology_zero
    (w : SpinePresentationRel q ⊕ (Fin q × Bool) → List (SpinePresentationGen q × Bool))
    (hw : ∀ j, FreeGroup.mk (w j) = cappedSpinePresentation q j)
    (hpos : ∀ j, 0 < (w j).length)
    (c : UF (orderCx (PresPos w)) (ptBase w) →₀ ℤ)
    (hc : Comb.bdry2 (uCover (orderCx (PresPos w)) (ptBase w)) c = 0) :
    orderNerveH2Class (PresPos w)
      (chain2 (univProj (X := orderCx (PresPos w)) (x₀ := ptBase w)) c)
      (by rw (config := { transparency := .default }) [bdry2_chain2, hc]; exact map_zero _) = 0 := by
  apply (orderNerveH2Class_eq_zero_iff _ _ _).mpr
  exact ⟨_, (cappedSpinePoset_path_cover_pushdown_boundary q w hw hpos c hc).symm⟩

/-- The actual universal-order-cover projection induces the zero map on second
integral order-nerve homology for the capped-spine model. -/
theorem cappedSpinePoset_homology_pushdown_map_zero
    (w : SpinePresentationRel q ⊕ (Fin q × Bool) → List (SpinePresentationGen q × Bool))
    (hw : ∀ j, FreeGroup.mk (w j) = cappedSpinePresentation q j)
    (hpos : ∀ j, 0 < (w j).length) :
    orderNerveH2Map uOrderEnd (presUniversalEnd_isPosetCover w hpos).mono = 0 := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H c =>
    change orderNerveH2Map uOrderEnd (presUniversalEnd_isPosetCover w hpos).mono
      (orderNerveH2Class _ c.val c.property) = 0
    rw (config := { transparency := .default }) [orderNerveH2Map_class]
    apply (orderNerveH2Class_eq_zero_iff _ _ _).mpr
    exact ⟨_, (cappedSpinePoset_weak_cycle_pushdown_boundary q w hw hpos
      c.val c.property).symm⟩

end FiniteChains.Davis.Genus
