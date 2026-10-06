import RequestProject.PresRelatorCircleEmbedding
import RequestProject.OrderNerveConeBallNaturality
import RequestProject.PresConeBall
import RequestProject.RelatorCircleBoundaryNaturality

/-! A literal presentation embedding preserves the actual parameters of
each old cone disk as soon as its circle parametrization is preserved. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel.PresWordEmbedding
open Comb RelativeAttachment
open scoped Classical

variable {A B J K : Type} {w : J → List (A × Bool)} {v : K → List (B × Bool)}
  (h : PresWordEmbedding w v) (j : J)

def coneLowerMap : Set.Iic (apexOf w j) ↪o Set.Iic (apexOf v (h.cell j)) where
  toFun x := ⟨h.posMap x.val, h.posMap.monotone x.property⟩
  inj' := fun _ _ he => Subtype.ext (h.posMap.injective (congrArg Subtype.val he))
  map_rel_iff' := h.posMap.le_iff_le

theorem coneLowerMap_withTop (p : WithTop (RelatorCircle w j)) :
    h.coneLowerMap j (lowerConeOrderIso (apexOf w j) (PresModel.relatorCircleOrderIso w j) p) =
      lowerConeOrderIso (apexOf v (h.cell j)) (PresModel.relatorCircleOrderIso v (h.cell j))
        ((h.relatorCircleOrderIso j).withTopCongr p) := by
  induction p using WithTop.recTopCoe with
  | top => rfl
  | coe p => rfl

theorem coneLowerMap_realization_withTop (x : orderNerveRealization (WithTop (RelatorCircle w j))) :
    orderNerveRealizationMap (h.coneLowerMap j) (h.coneLowerMap j).monotone
      (orderNerveRealizationOrderIso
        (lowerConeOrderIso (apexOf w j) (PresModel.relatorCircleOrderIso w j)) x) =
      orderNerveRealizationOrderIso
        (lowerConeOrderIso (apexOf v (h.cell j)) (PresModel.relatorCircleOrderIso v (h.cell j)))
        (orderNerveRealizationOrderIso (h.relatorCircleOrderIso j).withTopCongr x) := by
  change orderNerveRealizationMap _ _ (orderNerveRealizationMap _ _ x) =
    orderNerveRealizationMap _ _ (orderNerveRealizationMap _ _ x)
  rw [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
  have hf : (h.coneLowerMap j ∘
      lowerConeOrderIso (apexOf w j) (PresModel.relatorCircleOrderIso w j)) =
      (lowerConeOrderIso (apexOf v (h.cell j)) (PresModel.relatorCircleOrderIso v (h.cell j)) ∘
        (h.relatorCircleOrderIso j).withTopCongr) :=
    funext (h.coneLowerMap_withTop j)
  exact orderNerveRealizationMap_congr _ _ hf x

variable (hn : 0 < (w j).length) (hn' : 0 < (v (h.cell j)).length)

local instance sourceCircleFintype : Fintype (RelatorCircle w j) := Fintype.ofFinite _
local instance targetCircleFintype : Fintype (RelatorCircle v (h.cell j)) := Fintype.ofFinite _
private def sourceCircleNonempty : Nonempty (RelatorCircle w j) :=
  relatorCircle_nonempty w j (List.ne_nil_of_length_pos hn)
private def targetCircleNonempty : Nonempty (RelatorCircle v (h.cell j)) :=
  relatorCircle_nonempty v (h.cell j) (List.ne_nil_of_length_pos hn')

theorem presConeBallHomeomorph_natural_of_boundary
    (hb : ∀ x, relatorCircleBoundaryHomeomorph v (h.cell j) hn'
      (h.relatorCircleRealizationMap j x) = relatorCircleBoundaryHomeomorph w j hn x)
    (x : orderNerveRealization (Set.Iic (apexOf w j))) :
    presConeBallHomeomorph v (h.cell j) hn'
      (orderNerveRealizationMap (h.coneLowerMap j) (h.coneLowerMap j).monotone x) =
      presConeBallHomeomorph w j hn x := by
  letI : Nonempty (RelatorCircle w j) := relatorCircle_nonempty w j (List.ne_nil_of_length_pos hn)
  letI : Nonempty (RelatorCircle v (h.cell j)) :=
    relatorCircle_nonempty v (h.cell j) (List.ne_nil_of_length_pos hn')
  let e₀ := orderNerveRealizationOrderIso
    (lowerConeOrderIso (apexOf w j) (PresModel.relatorCircleOrderIso w j))
  obtain ⟨y, rfl⟩ := e₀.surjective x
  rw [coneLowerMap_realization_withTop]
  change orderNerveWithTopBallHomeomorph (relatorCircleBoundaryHomeomorph v (h.cell j) hn')
      ((orderNerveRealizationOrderIso
        (lowerConeOrderIso (apexOf v (h.cell j)) (PresModel.relatorCircleOrderIso v (h.cell j)))).symm
        (orderNerveRealizationOrderIso
          (lowerConeOrderIso (apexOf v (h.cell j)) (PresModel.relatorCircleOrderIso v (h.cell j)))
          (orderNerveRealizationOrderIso (h.relatorCircleOrderIso j).withTopCongr y))) =
    orderNerveWithTopBallHomeomorph (relatorCircleBoundaryHomeomorph w j hn) (e₀.symm (e₀ y))
  rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]
  exact orderNerveWithTopBallHomeomorph_natural (h.relatorCircleOrderIso j)
    (relatorCircleBoundaryHomeomorph w j hn) (relatorCircleBoundaryHomeomorph v (h.cell j) hn') hb y

theorem presConeBallHomeomorph_natural
    (x : orderNerveRealization (Set.Iic (apexOf w j))) :
    presConeBallHomeomorph v (h.cell j) hn'
      (orderNerveRealizationMap (h.coneLowerMap j) (h.coneLowerMap j).monotone x) =
      presConeBallHomeomorph w j hn x :=
  h.presConeBallHomeomorph_natural_of_boundary j hn hn'
    (h.relatorCircleBoundaryHomeomorph_natural j hn hn') x

end FiniteChains.PresModel.PresWordEmbedding
