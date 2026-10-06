import RequestProject.PresWordEmbedding
import RequestProject.PresRealizationWordDisks
import RequestProject.RelatorCircleBoundaryHomeomorph

/-! Restrict a literal presentation-word embedding to each actual
relator circle. Positions, cyclic indices, and the letter-reading map
are retained exactly. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel.PresWordEmbedding
open Comb
open scoped Topology

variable {A B J K : Type} {w : J → List (A × Bool)} {v : K → List (B × Bool)}
  (h : PresWordEmbedding w v)

def relatorCircleMap (j : J) : RelatorCircle w j ↪o RelatorCircle v (h.cell j) where
  toFun x := ⟨h.circleFun x.val, by
    constructor
    · exact congrArg h.cell x.property.1
    · change x.val.2.1 < (v (h.cell j)).length
      rw (config := { transparency := .default }) [h.word_length]
      exact x.property.2⟩
  inj' := fun _ _ he => Subtype.ext (h.circleFun_injective (congrArg Subtype.val he))
  map_rel_iff' := h.circleFun_le_iff _ _

@[simp] theorem relatorCircleMap_val (j : J) (x : RelatorCircle w j) :
    (h.relatorCircleMap j x).val = h.circleFun x.val := rfl

@[simp] theorem relatorCircleMap_position (j : J) (x : RelatorCircle w j) :
    (h.relatorCircleMap j x).val.2 = x.val.2 := rfl

@[simp] theorem relatorCircleMap_index (j : J) (x : RelatorCircle w j) :
    (relatorCircleIndexEquiv v (h.cell j) (h.relatorCircleMap j x)).val =
      (relatorCircleIndexEquiv w j x).val := rfl

theorem relatorCircleMap_point (j : J) (k : Fin (w j).length) (t : CPos) :
    h.relatorCircleMap j (relatorCirclePoint w j k t) =
      relatorCirclePoint v (h.cell j) ⟨k.val, by rw (config := { transparency := .default }) [h.word_length]; exact k.isLt⟩ t := rfl

theorem relatorCircleMap_surjective (j : J) : Function.Surjective (h.relatorCircleMap j) := by
  intro y
  let k : Fin (w j).length := ⟨y.val.2.1, by
    rw (config := { transparency := .default }) [← h.word_length j]
    exact y.property.2⟩
  refine ⟨relatorCirclePoint w j k y.val.2.2, ?_⟩
  apply Subtype.ext
  exact Prod.ext y.property.1.symm rfl

def relatorCircleOrderIso (j : J) : RelatorCircle w j ≃o RelatorCircle v (h.cell j) where
  toEquiv := Equiv.ofBijective (h.relatorCircleMap j)
    ⟨(h.relatorCircleMap j).injective, h.relatorCircleMap_surjective j⟩
  map_rel_iff' := (h.relatorCircleMap j).le_iff_le

def relatorCircleRealizationMap (j : J) :
    C(orderNerveRealization (RelatorCircle w j), orderNerveRealization (RelatorCircle v (h.cell j))) :=
  ⟨orderNerveRealizationMap (h.relatorCircleMap j) (h.relatorCircleMap j).monotone,
    (orderNerveRealizationMap (h.relatorCircleMap j) (h.relatorCircleMap j).monotone).hom.continuous⟩

theorem presCircleWordMap_natural (j : J) (x : orderNerveRealization (RelatorCircle w j)) :
    orderNerveRealizationMap h.roseMap h.roseMap.monotone (presCircleWordMap w j x) =
      presCircleWordMap v (h.cell j) (h.relatorCircleRealizationMap j x) := by
  change orderNerveRealizationMap h.roseMap h.roseMap.monotone
      (orderNerveRealizationMap (fun c : RelatorCircle w j => aFun w c.val)
        (fun _ _ h => aFun_monotone w h) x) =
    orderNerveRealizationMap (fun c : RelatorCircle v (h.cell j) => aFun v c.val)
      (fun _ _ h => aFun_monotone v h)
      (orderNerveRealizationMap (h.relatorCircleMap j) (h.relatorCircleMap j).monotone x)
  rw (config := { transparency := .default }) [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
  have hf : (h.roseMap ∘ (fun c : RelatorCircle w j => aFun w c.val)) =
      ((fun c : RelatorCircle v (h.cell j) => aFun v c.val) ∘ h.relatorCircleMap j) := by
    funext c
    exact (h.attaching_map c.val).symm
  exact orderNerveRealizationMap_congr _ _ hf x

end FiniteChains.PresModel.PresWordEmbedding
