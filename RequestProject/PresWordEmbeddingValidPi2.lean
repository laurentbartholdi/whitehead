module

public import RequestProject.PresWordEmbeddingFoxPi2
public import RequestProject.PresWordEmbeddingTopology
public import RequestProject.PresWordEmbeddingPi1
public import RequestProject.PresValidPi2

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel.PresWordEmbedding
open Comb
variable {α β J K : Type}
variable {w : J → List (α × Bool)} {v : K → List (β × Bool)}
  (h : PresWordEmbedding w v)

noncomputable def realizationMap :
    C(orderNerveRealization (PresPos w), orderNerveRealization (PresPos v)) :=
  ⟨orderNerveRealizationMap h.posMap h.posMap.monotone,
    (orderNerveRealizationMap h.posMap h.posMap.monotone).hom.continuous⟩

/-- Retraction after the actual full map restricts exactly to the finite model map. -/
theorem validRealizationMap_factor :
    (presValidRealizationRetraction v).comp
      (h.realizationMap.comp (presValidRealizationInclusion w)) = h.validRealizationMap := by
  apply ContinuousMap.ext
  intro x
  change orderNerveRealizationMap (presValidRetraction v) (presValidRetraction v).monotone
    (orderNerveRealizationMap h.posMap h.posMap.monotone
      (orderNerveRealizationMap (Subtype.val : ValidPresPos w → PresPos w) (fun _ _ h => h) x)) = _
  rw (config := { transparency := .default }) [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
  have he : ((presValidRetraction v ∘ h.posMap) ∘ (Subtype.val : ValidPresPos w → PresPos w)) =
      h.validMap := funext h.validMap_retraction
  simp only [he]
  rfl

/-- The actual pi2 vanishing passes to the retained finite model. -/
theorem valid_killsPi2_of_full (hk : Whitehead.KillsPi2 h.realizationMap) :
    Whitehead.KillsPi2 h.validRealizationMap := by
  rw (config := { transparency := .default }) [← h.validRealizationMap_factor]
  intro x p
  have hn := Whitehead.mapSquare_homotopic (presValidRealizationRetraction v)
    (hk (presValidRealizationInclusion w x) (Whitehead.mapSquare (presValidRealizationInclusion w) p))
  simpa only [Whitehead.mapSquare_const, Whitehead.mapSquare_comp] using hn

variable [DecidableEq α]
  (ρ : J → FreeGroup α) (σ : K → FreeGroup β)
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hv : ∀ k, FreeGroup.mk (v k) = σ k)
  (hwp : ∀ j, 0 < (w j).length) (hvp : ∀ k, 0 < (v k).length)

include hw hv hwp hvp in
/-- A checked Fox-cycle calculation now implies the genuine pi2 condition for
the actual finite-model CW inclusion, with no comparison premise. -/
theorem valid_killsPi2_of_fox
    (hz : ∀ z : LinearMap.ker ((coverSecondBoundary (relSub ρ) ρ).restrictScalars ℤ),
      Finsupp.mapDomain (Prod.map (h.groupHom ρ σ hw hv) h.cell)
        (groupCellChainEquiv.symm z.val) = 0) :
    Whitehead.KillsPi2 h.validRealizationMap :=
  h.valid_killsPi2_of_full ((h.killsPi2_iff_fox hwp hvp ρ σ hw hv).mpr hz)

end FiniteChains.PresModel.PresWordEmbedding
