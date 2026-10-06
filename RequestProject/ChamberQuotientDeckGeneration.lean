import RequestProject.ChamberQuotientEquivariantGeneration

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

omit [Fintype V] in
/-- The translations in quotient cycle generation are the actual deck action. -/
theorem qBaseDeckCoverFaceMap_eq_deckF {a : Qpos A X att} (b : QLiftedBase a)
    (g : Pi1 (orderCx (Qpos A X att)) a)
    (hc : IsConnected (orderCx (Qpos A X att))) (hx : IsConnected (orderCx X))
    (t : UF (orderCx X) (qBaseCoverEnd (X := X) a b)) :
    qBaseDeckCoverFaceMap b g hc hx t =
      deckF g (qBaseDeckCoverFaceMap b 1 hc hx t) := by
  apply Subtype.ext
  apply Prod.ext
  · change deckV g _ = deckV g (deckV 1 _)
    rw [deckV_one]
  · apply Subtype.ext
    change (uOrderEnd (deckV g _), uOrderEnd (deckV g _), uOrderEnd (deckV g _)) =
      (uOrderEnd (deckV 1 _), uOrderEnd (deckV 1 _), uOrderEnd (deckV 1 _))
    simp only [deckV_one]
    change (endV (deckV g _), endV (deckV g _), endV (deckV g _)) = _
    simp only [endV_deckV]
    rfl

end FiniteChains.Davis
