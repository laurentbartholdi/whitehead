import RequestProject.PresCylinderInclusionPi1
import RequestProject.RoseRootedLoops
import RequestProject.PresPosetReadingSurjective

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool))

/-- Inclusion of the genuine rose generator map is the actual marked free-group map. -/
theorem roseLoopHom_inclusion :
    (pi1Map (orderCxMap (iRose w) (iRose_monotone w)) Rose.base).comp
      (loopHom (roseGeneratorLoop (α := α))) = alphaFree w := by
  apply FreeGroup.ext_hom
  intro i
  rw [MonoidHom.comp_apply, loopHom_of]
  exact (show (pi1Map (orderCxMap (iRose w) (iRose_monotone w)) Rose.base)
    (Pi1.mk (roseGeneratorLoop i)) = genClass w i from rfl).trans
      (alphaFree_of w i).symm

/-- The actual free-group marking surjects onto the presentation fundamental group. -/
theorem alphaFree_surjective (hpos : ∀ j, 0 < (w j).length) :
    Function.Surjective (alphaFree w) := by
  intro z
  obtain ⟨q, hq⟩ := presRoseInclusion_pi1_surjective w hpos Rose.base z
  obtain ⟨p, hp⟩ := roseLoopHom_surjective q
  refine ⟨p, ?_⟩
  have h := DFunLike.congr_fun (roseLoopHom_inclusion w) p
  rw [MonoidHom.comp_apply, hp, hq] at h
  exact h.symm

variable (ρ : J → FreeGroup α) (hw : ∀ j, FreeGroup.mk (w j) = ρ j)

/-- The marked presentation comparison is surjective for actual nonempty relator words. -/
theorem alphaHomW_surjective (hpos : ∀ j, 0 < (w j).length) :
    Function.Surjective (alphaHomW ρ w hw) := by
  intro z
  obtain ⟨p, hp⟩ := alphaFree_surjective w hpos z
  exact ⟨QuotientGroup.mk p, hp⟩

/-- Reading and marking are actual inverse maps on the presentation fundamental group. -/
theorem alphaHomW_readingPresW (hpos : ∀ j, 0 < (w j).length)
    (z : Pi1 (orderCx (PresPos w)) (ptBase w)) :
    alphaHomW ρ w hw (readingPresW ρ w hw z) = z := by
  obtain ⟨p, rfl⟩ := alphaHomW_surjective w ρ hw hpos z
  rw [readingPresW_alphaHomW]

/-- The actual presentation reading is injective, without a group-comparison premise. -/
theorem readingPresW_injective (hpos : ∀ j, 0 < (w j).length) :
    Function.Injective (readingPresW ρ w hw) :=
  Function.LeftInverse.injective (alphaHomW_readingPresW w ρ hw hpos)

/-- The marked presentation group is isomorphic to the actual order-complex fundamental group. -/
noncomputable def presPosetGroupEquiv (hpos : ∀ j, 0 < (w j).length) :
    PresGroup ρ ≃* Pi1 (orderCx (PresPos w)) (ptBase w) :=
  MulEquiv.ofBijective (alphaHomW ρ w hw)
    ⟨alphaHomW_injective ρ w hw, alphaHomW_surjective w ρ hw hpos⟩

end FiniteChains.PresModel
