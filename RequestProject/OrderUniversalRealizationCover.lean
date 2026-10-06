module

public import RequestProject.OrderNerveRealizationRegular
public import RequestProject.OrderUniversalPosetCover
public import RequestProject.OrderUniversalDeck
public import RequestProject.OrderUniversalPosetCells

@[expose] public section

/-! Genuine regular topological covers from the constructed path-class order cover. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open Topology

variable {P : Type} [PartialOrder P] (a : P)

/-- The actual endpoint projection on geometric realizations. -/
noncomputable def uOrderRealizationProjection :
    C(orderNerveRealization (UOrder P a), orderNerveRealization P) :=
  ⟨orderNerveRealizationMap uOrderEnd uOrderEnd_monotone,
    (orderNerveRealizationMap uOrderEnd uOrderEnd_monotone).hom.continuous⟩

theorem uOrderRealizationProjection_isCoveringMap (hc : IsConnected (orderCx P)) :
    IsCoveringMap (uOrderRealizationProjection a) :=
  (uOrderEnd_isPosetCover (a := a) hc).realizationMap_isCoveringMap

theorem uOrderRealizationProjection_surjective (hc : IsConnected (orderCx P)) :
    Function.Surjective (uOrderRealizationProjection a) :=
  (uOrderEnd_isPosetCover (a := a) hc).realizationMap_surjective

/-- Every two vertices in an endpoint fiber are exchanged by an actual order deck isomorphism. -/
theorem uOrderEnd_deck_transitive (v w : UOrder P a) (h : uOrderEnd v = uOrderEnd w) :
    ∃ e : UOrder P a ≃o UOrder P a,
      (∀ p, uOrderEnd (e p) = uOrderEnd p) ∧ e v = w := by
  obtain ⟨g, hg, _⟩ :=
    (isRegular_univProj (X := orderCx P) (x₀ := a)).simply_transitive v w h
  exact ⟨uOrderDeckOrderIso g, endV_deckV g, hg⟩

/-- The actual endpoint cover is regular in the precise topological sense of Challenge. -/
theorem uOrderRealizationProjection_regular (hc : IsConnected (orderCx P)) :
    Whitehead.Regular (uOrderRealizationProjection a) :=
  (uOrderEnd_isPosetCover (a := a) hc).realizationMap_regular (uOrderEnd_deck_transitive a)

/-- Endpoints of an actual universal-cover edge are joined in the actual realization. -/
theorem uOrderRealization_edge_joined (e : UE (orderCx P) a) :
    Joined (orderNerveRealizationVertex (P := UOrder P a) (uSrc e))
      (orderNerveRealizationVertex (P := UOrder P a) (uTgt e)) := by
  obtain ⟨t, rfl⟩ := uOrderEdge_surjective e
  have ht : uTgt (uOrderEdge t) = t.val.2 := t.property.2
  change Joined (orderNerveRealizationVertex t.val.1)
    (orderNerveRealizationVertex (uTgt (uOrderEdge t)))
  rw [ht]
  exact orderNerveRealizationVertex_joined_of_le t.property

/-- Combinatorial universal-cover paths give actual continuous joinedness upstairs. -/
theorem uOrderRealization_path_joined {v w : UOrder P a}
    {p : List ((uCover (orderCx P) a).E × Bool)}
    (hp : IsPath (uCover (orderCx P) a).src (uCover (orderCx P) a).tgt p v w) :
    Joined (orderNerveRealizationVertex v) (orderNerveRealizationVertex w) := by
  induction p generalizing v with
  | nil =>
    change v = w at hp
    subst w
    exact Joined.refl _
  | cons e p ih =>
    rcases hp with ⟨rfl, hp⟩
    have he : Joined
        (orderNerveRealizationVertex (P := UOrder P a)
          (germSrc (uCover (orderCx P) a).src (uCover (orderCx P) a).tgt e))
        (orderNerveRealizationVertex (P := UOrder P a)
          (germTgt (uCover (orderCx P) a).src (uCover (orderCx P) a).tgt e)) := by
      rcases e with ⟨e, b⟩
      cases b
      · exact (uOrderRealization_edge_joined a e).symm
      · exact uOrderRealization_edge_joined a e
    exact he.trans (ih hp)

/-- The actual realization upstairs is path connected; no additional premise is required. -/
theorem uOrderRealization_pathConnectedSpace :
    PathConnectedSpace (orderNerveRealization (UOrder P a)) where
  nonempty := ⟨orderNerveRealizationVertex (P := UOrder P a) (UV.base (orderCx P) a)⟩
  joined x y := by
    obtain ⟨n, s, z, hx⟩ := orderNerveRealizationSimplex_jointly_surjective (UOrder P a) x
    obtain ⟨m, t, w, hy⟩ := orderNerveRealizationSimplex_jointly_surjective (UOrder P a) y
    have hs := orderNerveRealizationSimplex_joined_vertex s z (0 : Fin (n.len + 1))
    have ht := orderNerveRealizationSimplex_joined_vertex t w (0 : Fin (m.len + 1))
    rw [hx] at hs
    rw [hy] at ht
    obtain ⟨p, hp⟩ := isConnected_univCover (X := orderCx P) (x₀ := a) (s.obj 0) (t.obj 0)
    exact hs.trans ((uOrderRealization_path_joined a hp).trans ht.symm)

end FiniteChains.Comb
