module

public import RequestProject.OrderComponentLabels
public import RequestProject.OrderPosetCovering

@[expose] public section

/-! Every actual reachable component of a poset cover covers a connected base. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}

abbrev OrderReachComponent (P : Type u) [PartialOrder P] (a : P) :=
  {p : P // Reach (orderCx P) a p}

def orderComponentProjection (f : P → Q) (a : P) : OrderReachComponent P a → Q :=
  fun p => f p.1

theorem IsPosetCover.reachableRestriction (hf : IsPosetCover f)
    (hconn : IsConnected (orderCx Q)) (a : P) :
    IsPosetCover (orderComponentProjection f a) where
  mono := fun _ _ h => hf.mono h
  surj q := by
    obtain ⟨l, hl⟩ := hconn (f a) q
    obtain ⟨m, b, hm, hmap⟩ := exists_liftPathAt (isCovering_orderCxMap hf) l a q hl
    have hpath := isPath_mapPath (orderCxMap f hf.mono) hm
    rw [hmap] at hpath
    have hfb : f b = q := (endpt_eq_of_isPath hpath).symm.trans (endpt_eq_of_isPath hl)
    exact ⟨⟨b, ⟨m, hm⟩⟩, hfb⟩
  up p q hpq := by
    obtain ⟨r, ⟨hpr, hfr⟩, hu⟩ := hf.up p.1 q hpq
    have hr : Reach (orderCx P) a r := p.2.trans_path (isPath_ordPos hpr)
    refine ⟨⟨r, hr⟩, ⟨hpr, hfr⟩, ?_⟩
    rintro s ⟨hps, hfs⟩
    exact Subtype.ext (hu s.1 ⟨hps, hfs⟩)
  down p q hqp := by
    obtain ⟨r, ⟨hrp, hfr⟩, hu⟩ := hf.down p.1 q hqp
    have hr : Reach (orderCx P) a r := p.2.trans_path (isPath_ordNeg hrp)
    refine ⟨⟨r, hr⟩, ⟨hrp, hfr⟩, ?_⟩
    rintro s ⟨hsp, hfs⟩
    exact Subtype.ext (hu s.1 ⟨hsp, hfs⟩)

theorem orderReachComponent_simplyConnected (hf : IsPosetCover f)
    (hconn : IsConnected (orderCx Q)) (hsc : SimplyConnected (orderCx P)) (a : P) :
    SimplyConnected (orderCx (OrderReachComponent P a)) := by
  let incl := orderCxMap (Subtype.val : OrderReachComponent P a → P) (fun _ _ h => h)
  let p := orderCxMap (orderComponentProjection f a) (hf.reachableRestriction hconn a).mono
  have hp : IsCovering p := isCovering_orderCxMap (hf.reachableRestriction hconn a)
  intro v m hm
  have ht := mapPath_htpy (orderCxMap f hf.mono)
    (hsc v.1 (mapPath incl m) (isPath_mapPath incl hm))
  have hnull : Htpy (orderCx Q) (p.onV v) (p.onV v) (mapPath p m) [] := by
    simpa only [mapPath, List.map_map, List.map_nil, p, incl, orderComponentProjection, orderCxMap, subposetHom, Function.comp_def] using ht
  obtain ⟨m', _, hmap, hhtpy⟩ := lift_htpy hp hm hnull
  have hnil : m' = [] := List.map_eq_nil_iff.mp hmap
  rwa [hnil] at hhtpy

theorem orderReachComponent_isConnected (hf : IsPosetCover f)
    (hconn : IsConnected (orderCx Q)) (a : P) :
    IsConnected (orderCx (OrderReachComponent P a)) := by
  let root : OrderReachComponent P a := ⟨a, reach_self (orderCx P) a⟩
  let incl := orderCxMap (Subtype.val : OrderReachComponent P a → P) (fun _ _ h => h)
  let p := orderCxMap (orderComponentProjection f a) (hf.reachableRestriction hconn a).mono
  have hp : IsCovering p := isCovering_orderCxMap (hf.reachableRestriction hconn a)
  have hreach : ∀ v : OrderReachComponent P a,
      ∃ m, IsPath (orderCx (OrderReachComponent P a)).src
        (orderCx (OrderReachComponent P a)).tgt m root v := by
    intro v
    obtain ⟨l, hl⟩ := v.2
    obtain ⟨m, w, hm, hmap⟩ := exists_liftPathAt hp
      (mapPath (orderCxMap f hf.mono) l) root (f v.1)
      (isPath_mapPath (orderCxMap f hf.mono) hl)
    have hm' := isPath_mapPath incl hm
    have he : mapPath (orderCxMap f hf.mono) (mapPath incl m) =
        mapPath (orderCxMap f hf.mono) l := by
      simpa only [mapPath, List.map_map, List.map_nil, p, incl, orderComponentProjection, orderCxMap, subposetHom, Function.comp_def] using hmap
    have hml : mapPath incl m = l := liftPath_unique (isCovering_orderCxMap hf)
      (mapPath incl m) l a w.1 v.1 hm' hl he
    have hw : w = v := by
      apply Subtype.ext
      rw [hml] at hm'
      exact isPath_endpoint_eq hm' hl
    exact ⟨m, hw ▸ hm⟩
  intro v w
  obtain ⟨m, hm⟩ := hreach v
  obtain ⟨n, hn⟩ := hreach w
  exact ⟨revPath m ++ n, (isPath_revPath hm).append hn⟩

end FiniteChains.Comb
