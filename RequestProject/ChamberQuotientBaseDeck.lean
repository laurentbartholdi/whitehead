import RequestProject.ChamberQuotientBaseComponents
import RequestProject.OrderUniversalDeck

/-! Deck transformations permute the actual lifted base components transitively. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X} {a : Qpos A X att}

def qBaseDeckOrderIso (g : Pi1 (orderCx (Qpos A X att)) a) : QLiftedBase a ≃o QLiftedBase a where
  toFun v := ⟨uOrderDeck g v.1, by
    rw [uOrderDeck_end]
    exact v.2⟩
  invFun v := ⟨uOrderDeck g⁻¹ v.1, by
    rw [uOrderDeck_end]
    exact v.2⟩
  left_inv v := by
    apply Subtype.ext
    change deckV g⁻¹ (deckV g v.1) = v.1
    rw [← deckV_mul, inv_mul_cancel, deckV_one]
  right_inv v := by
    apply Subtype.ext
    change deckV g (deckV g⁻¹ v.1) = v.1
    rw [← deckV_mul, mul_inv_cancel, deckV_one]
  map_rel_iff' {v w} := (uOrderDeckOrderIso g).map_rel_iff

omit [Fintype V] in
theorem qBaseDeck_preserves_projection (g : Pi1 (orderCx (Qpos A X att)) a)
    (v : QLiftedBase a) :
    qBaseCoverEnd (X := X) a (qBaseDeckOrderIso g v) = qBaseCoverEnd (X := X) a v := by
  have h := (qBaseCoverEnd_spec a (qBaseDeckOrderIso g v)).trans
    ((uOrderDeck_end g v.1).trans (qBaseCoverEnd_spec a v).symm)
  exact Sum.inr.inj h

omit [Fintype V] in
/-- Every lifted base component is a deck translate of the component of `b`.
The witness is constructed by lifting a base path and then using regularity
on the common endpoint fiber of the actual universal cover. -/
theorem qBase_components_deck_transitive
    (hc : IsConnected (orderCx (Qpos A X att))) (hx : IsConnected (orderCx X))
    (b v : QLiftedBase a) :
    ∃ g : Pi1 (orderCx (Qpos A X att)) a,
      Reach (orderCx (QLiftedBase a)) (qBaseDeckOrderIso g b) v := by
  let beta := orderCxMap (qBaseCoverEnd a) (qBaseCoverEnd_isPosetCover a hc).mono
  have hcov : IsCovering beta := isCovering_orderCxMap (qBaseCoverEnd_isPosetCover a hc)
  obtain ⟨l, hl⟩ := hx (qBaseCoverEnd (X := X) a b) (qBaseCoverEnd (X := X) a v)
  obtain ⟨m, w, hm, hmap⟩ := exists_liftPathAt hcov l b _ hl
  have hproj := isPath_mapPath beta hm
  rw [hmap] at hproj
  have he : qBaseCoverEnd (X := X) a w = qBaseCoverEnd (X := X) a v :=
    isPath_endpoint_eq hproj hl
  have hend : uOrderEnd w.1 = uOrderEnd v.1 :=
    (qBaseCoverEnd_spec a w).symm.trans
      ((congrArg (qNew (A := A) (att := att)) he).trans (qBaseCoverEnd_spec a v))
  obtain ⟨g, hg, _⟩ := (isRegular_univProj (X := orderCx (Qpos A X att))
    (x₀ := a)).simply_transitive w.1 v.1 hend
  have hgw : qBaseDeckOrderIso g w = v := Subtype.ext hg
  let deck := orderCxMap (qBaseDeckOrderIso g) (qBaseDeckOrderIso g).monotone
  have hpath := isPath_mapPath deck hm
  change IsPath (orderCx (QLiftedBase a)).src (orderCx (QLiftedBase a)).tgt
    (mapPath deck m) (qBaseDeckOrderIso g b) (qBaseDeckOrderIso g w) at hpath
  rw [hgw] at hpath
  exact ⟨g, mapPath deck m, hpath⟩

end FiniteChains.Davis
