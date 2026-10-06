module

public import RequestProject.PresWordEmbedding
public import RequestProject.PresPosetGroupEquiv
public import RequestProject.OrderCxNullTransfer
public import RequestProject.ZeroPi2Descent

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel.PresWordEmbedding
open Comb
variable {α β J K : Type}
variable {w : J → List (α × Bool)} {v : K → List (β × Bool)}
  (h : PresWordEmbedding w v)

/-- Renaming the actual four-edge generator loop renames its generator. -/
theorem pi1Map_alphaFree :
    (pi1Map (orderCxMap h.posMap h.posMap.monotone) (ptBase w)).comp (alphaFree w) =
      (alphaFree v).comp (FreeGroup.map h.gen) := by
  apply FreeGroup.ext_hom
  intro a
  change pi1Map (orderCxMap h.posMap h.posMap.monotone) (ptBase w)
    (alphaFree w (FreeGroup.of a)) = alphaFree v (FreeGroup.of (h.gen a))
  rw [alphaFree_of, alphaFree_of]
  rfl

/-- Killing the marked target generators kills every based loop in the full model. -/
theorem pi1Trivial_posMap_of_generators (σ : K → FreeGroup β)
    (hv : ∀ k, FreeGroup.mk (v k) = σ k) (hw : ∀ j, 0 < (w j).length)
    (hz : ∀ a, (QuotientGroup.mk (FreeGroup.of (h.gen a)) : PresGroup σ) = 1) :
    Pi1Trivial (orderCxMap h.posMap h.posMap.monotone) := by
  let F := orderCxMap h.posMap h.posMap.monotone
  have hg (a : α) : genClass v (h.gen a) = 1 := by
    rw [← alphaHomW_gen σ v hv, hz, map_one]
  have hf : (alphaFree v).comp (FreeGroup.map h.gen) = 1 := by
    apply FreeGroup.ext_hom
    intro a
    change alphaFree v (FreeGroup.of (h.gen a)) = 1
    rw [alphaFree_of, hg]
  have hb (p : List ((orderCx (PresPos w)).E × Bool))
      (hp : IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt p (ptBase w) (ptBase w)) :
      Htpy (orderCx (PresPos v)) (ptBase v) (ptBase v) (mapPath F p) [] := by
    obtain ⟨a, ha⟩ := alphaFree_surjective w hw (Pi1.mk ⟨p, hp⟩)
    have he := DFunLike.congr_fun h.pi1Map_alphaFree a
    rw [hf] at he
    change pi1Map F (ptBase w) (alphaFree w a) = 1 at he
    rw [ha] at he
    exact Quotient.exact he
  intro x p hp
  obtain ⟨e, he⟩ := presPos_isConnected w (fun j => List.length_pos_iff.mp (hw j)) x (ptBase w)
  apply htpy_nil_of_conjugate (isPath_mapPath F he) (isPath_mapPath F hp)
  have hloop := (isPath_revPath he).append (hp.append he)
  have hn := hb (revPath e ++ p ++ e) (by simpa only [List.append_assoc] using hloop)
  simp only [mapPath_append, mapPath_revPath] at hn
  convert hn using 1 <;> rfl

/-- Retraction of the target returns the given valid-position map exactly. -/
theorem validMap_retraction (p : ValidPresPos w) :
    presValidRetraction v (h.posMap p.val) = h.validMap p :=
  presValidRetraction_val v (h.validMap p)

/-- Restricting both ends to their retained vertices preserves triviality on pi1. -/
theorem pi1Trivial_validMap (ht : Pi1Trivial (orderCxMap h.posMap h.posMap.monotone)) :
    Pi1Trivial (orderCxMap h.validMap h.validMap.monotone) := by
  let I := orderCxMap (Subtype.val : ValidPresPos w → PresPos w) (fun _ _ h => h)
  let R := orderCxMap (presValidRetraction v) (presValidRetraction v).monotone
  let F := orderCxMap h.posMap h.posMap.monotone
  have he (p : List ((orderCx (ValidPresPos w)).E × Bool)) :
      mapPath R (mapPath F (mapPath I p)) = mapPath (orderCxMap h.validMap h.validMap.monotone) p := by
    simp only [mapPath, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro eb _
    refine Prod.ext ?_ rfl
    apply Subtype.ext
    exact Prod.ext (h.validMap_retraction _) (h.validMap_retraction _)
  intro x p hp
  have hn := mapPath_htpy R (ht x.val (mapPath I p) (isPath_mapPath I hp))
  rw [he, mapPath_nil] at hn
  simpa only [R, F, I, orderCxMap, h.validMap_retraction] using hn

theorem pi1Trivial_validMap_of_generators (σ : K → FreeGroup β)
    (hv : ∀ k, FreeGroup.mk (v k) = σ k) (hw : ∀ j, 0 < (w j).length)
    (hz : ∀ a, (QuotientGroup.mk (FreeGroup.of (h.gen a)) : PresGroup σ) = 1) :
    Pi1Trivial (orderCxMap h.validMap h.validMap.monotone) :=
  h.pi1Trivial_validMap (h.pi1Trivial_posMap_of_generators σ hv hw hz)

end FiniteChains.PresModel.PresWordEmbedding
