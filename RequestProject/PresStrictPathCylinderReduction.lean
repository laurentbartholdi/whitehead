import RequestProject.PresConeStrictExcursionReplacement

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool))

/-- Every strict lower vertex of an actual relator apex belongs to the actual cylinder. -/
theorem presCone_lower_mem_cylinder (j : J) (x : PresPos w) (hx : x < apexOf w j) :
    x ∈ coneAdjBaseSet (S := circSet w) := by
  obtain ⟨k, t, _, he⟩ := (presPos_lt_apex_iff w j x).mp hx
  exact ⟨cylOuter (aHom w) (TCirc.pt w j k t), he.symm⟩

/-- An included strict germ with cylinder endpoints lies in the actual cylinder. -/
theorem presStrictGerm_in_cylinder (e : (strictOrderCx (PresPos w)).E × Bool)
    (hs : germSrc (strictOrderCx (PresPos w)).src (strictOrderCx (PresPos w)).tgt e ∈ coneAdjBaseSet (S := circSet w))
    (ht : germTgt (strictOrderCx (PresPos w)).src (strictOrderCx (PresPos w)).tgt e ∈ coneAdjBaseSet (S := circSet w)) :
    PathIn (fun p => p ∈ coneAdjBaseSet (S := circSet w))
      (mapPath (strictOrderIncl (PresPos w)) [e]) := by
  rcases e with ⟨e, b⟩
  cases b <;> exact pathIn_cons (by constructor <;> assumption) (pathIn_nil _)

/-- Every actual strict presentation path with cylinder endpoints reduces to an actual cylinder path. -/
theorem exists_presStrictPath_cylinder_reduction (hpos : ∀ j, 0 < (w j).length)
    (p : List ((strictOrderCx (PresPos w)).E × Bool))
    (a b : PresPos w) (ha : a ∈ coneAdjBaseSet (S := circSet w)) (hb : b ∈ coneAdjBaseSet (S := circSet w))
    (hp : IsPath (strictOrderCx (PresPos w)).src (strictOrderCx (PresPos w)).tgt p a b) :
    ∃ q : List ((orderCx (PresPos w)).E × Bool),
      IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt q a b ∧
      PathIn (fun x => x ∈ coneAdjBaseSet (S := circSet w)) q ∧
      Htpy (orderCx (PresPos w)) a b (mapPath (strictOrderIncl (PresPos w)) p) q := by
  induction p using (measure List.length).wf.induction generalizing a b with
  | h p ih =>
    cases p with
    | nil =>
      subst b
      exact ⟨[], rfl, pathIn_nil _, Htpy.refl _⟩
    | cons e p =>
      obtain ⟨hea, hp⟩ := hp
      have hsingle : IsPath (strictOrderCx (PresPos w)).src (strictOrderCx (PresPos w)).tgt
          [e] a (germTgt (strictOrderCx (PresPos w)).src (strictOrderCx (PresPos w)).tgt e) := ⟨hea, rfl⟩
      cases ht : germTgt (strictOrderCx (PresPos w)).src (strictOrderCx (PresPos w)).tgt e with
      | inl t =>
        have hm : germTgt (strictOrderCx (PresPos w)).src (strictOrderCx (PresPos w)).tgt e ∈ coneAdjBaseSet (S := circSet w) :=
          ⟨t, ht.symm⟩
        obtain ⟨q, hq, hqc, hh⟩ := ih p (by change p.length < _; simp) _ b hm hb hp
        have hec := presStrictGerm_in_cylinder w e (hea ▸ ha) hm
        refine ⟨mapPath (strictOrderIncl (PresPos w)) [e] ++ q,
          (isPath_mapPath _ hsingle).append hq, pathIn_append hec hqc, ?_⟩
        simpa only [mapPath, List.map_cons, List.map_nil, List.singleton_append, strictOrderIncl, id_eq] using
          Htpy.append_congr (isPath_mapPath (strictOrderIncl (PresPos w)) hsingle)
            (isPath_mapPath (strictOrderIncl (PresPos w)) hp) (Htpy.refl _) hh
      | inr j =>
        cases p with
        | nil =>
          have hbe : b = apexOf w j := hp.symm.trans ht
          obtain ⟨t, htb⟩ := hb
          have hn : (Sum.inl t : PresPos w) = Sum.inr j := htb.trans hbe
          cases hn
        | cons d p =>
          obtain ⟨hds, hp⟩ := hp
          have hed := presCone_strictGerm_to_apex w j e ht
          have hdd := presCone_strictGerm_from_apex w j d (hds.symm.trans ht)
          rcases e with ⟨e, es⟩
          rcases d with ⟨d, ds⟩
          obtain ⟨rfl, he⟩ := hed
          obtain ⟨rfl, hd⟩ := hdd
          have hdc : d.val.1 ∈ coneAdjBaseSet (S := circSet w) := presCone_lower_mem_cylinder w j d.val.1 (hd ▸ d.property)
          obtain ⟨q, hq, hqc, hh⟩ := ih p (by change p.length < _; simp) d.val.1 b hdc hb hp
          obtain ⟨r, hr, hrc, hhr⟩ := exists_presCone_strictEdge_excursion_replacement w j (hpos j) e d he hd
          subst a
          refine ⟨r ++ q, hr.append hq, pathIn_append hrc hqc, ?_⟩
          simpa only [mapPath, List.map_cons, List.map_nil, List.cons_append, List.nil_append, strictOrderIncl, strictOrderCx, germSrc, if_true, id_eq] using
            Htpy.append_congr
              (isPath_mapPath (strictOrderIncl (PresPos w))
                (show IsPath (strictOrderCx (PresPos w)).src (strictOrderCx (PresPos w)).tgt
                  [(e, true), (d, false)] e.val.1 d.val.1 from ⟨rfl, he.trans hd.symm, rfl⟩))
              (isPath_mapPath (strictOrderIncl (PresPos w)) hp) hhr hh

/-- Every actual weak presentation path with cylinder endpoints reduces to an actual cylinder path. -/
theorem exists_presPath_cylinder_reduction (hpos : ∀ j, 0 < (w j).length)
    (p : List ((orderCx (PresPos w)).E × Bool))
    (a b : PresPos w) (ha : a ∈ coneAdjBaseSet (S := circSet w))
    (hb : b ∈ coneAdjBaseSet (S := circSet w))
    (hp : IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt p a b) :
    ∃ q : List ((orderCx (PresPos w)).E × Bool),
      IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt q a b ∧
      PathIn (fun x => x ∈ coneAdjBaseSet (S := circSet w)) q ∧
      Htpy (orderCx (PresPos w)) a b p q := by
  obtain ⟨q, hq, hc, hh⟩ := exists_presStrictPath_cylinder_reduction w hpos
    (normalizeOrdPath p) a b ha hb (normalizeOrdPath_isPath hp)
  exact ⟨q, hq, hc, (normalizeOrdPath_htpy hp).symm.trans hh⟩

end FiniteChains.PresModel
