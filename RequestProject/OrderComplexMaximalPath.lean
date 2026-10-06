module

public import RequestProject.OrderComplexBoundaryDetour
public import RequestProject.StrictOrderComplex

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable {P : Type} [PartialOrder P]

theorem germ_into_maximal_lt {C : P → Prop} {t : P}
    (hmax : ∀ x, C x → t ≤ x → x = t) (e : (orderCx P).E × Bool)
    (he : C e.1.1.1 ∧ C e.1.1.2)
    (ht : germTgt (orderCx P).src (orderCx P).tgt e = t)
    (hne : germSrc (orderCx P).src (orderCx P).tgt e ≠ t) :
    (germSrc (orderCx P).src (orderCx P).tgt e : P) < t := by
  obtain ⟨e, b⟩ := e
  cases b with
  | true =>
    change e.1.2 = t at ht
    change e.1.1 ≠ t at hne
    change e.1.1 < t
    exact lt_of_le_of_ne (ht ▸ e.2) hne
  | false =>
    change e.1.1 = t at ht
    change e.1.2 ≠ t at hne
    exact False.elim (hne (hmax e.1.2 he.2 (ht ▸ e.2)))

 theorem maximal_detour_germs {C : P → Prop} {t u v : P}
    (hmax : ∀ x, C x → t ≤ x → x = t)
    (hconn : ConnectedIn (fun x => C x ∧ x < t))
    (e f : (orderCx P).E × Bool)
    (he : IsPath (orderCx P).src (orderCx P).tgt [e] u t)
    (hf : IsPath (orderCx P).src (orderCx P).tgt [f] t v)
    (hC : PathIn C [e, f]) (hu : u ≠ t) (hv : v ≠ t) :
    ∃ l, IsPath (orderCx P).src (orderCx P).tgt l u v ∧
      PathIn (fun x => C x ∧ x ≠ t) l ∧ Htpy (orderCx P) u v [e, f] l := by
  have heC := (pathIn_of_cons hC).1
  have hfC := (pathIn_of_cons (pathIn_of_cons hC).2).1
  have heends := germ_ends heC
  have hfends := germ_ends hfC
  have hes : germSrc (orderCx P).src (orderCx P).tgt e = u := he.1.symm
  have het : germTgt (orderCx P).src (orderCx P).tgt e = t := he.2
  have hfs : germSrc (orderCx P).src (orderCx P).tgt f = t := hf.1.symm
  have hft : germTgt (orderCx P).src (orderCx P).tgt f = v := hf.2
  have hut : u < t := by
    simpa only [hes] using germ_into_maximal_lt hmax e heC het (hes ▸ hu)
  have hvt : v < t := by
    have hrC : C (revGerm f).1.1.1 ∧ C (revGerm f).1.1.2 := hfC
    have hr := germ_into_maximal_lt hmax (revGerm f) hrC
      (by simpa using hfs) (by simpa [hft] using hv)
    rwa [germSrc_revGerm, hft] at hr
  obtain ⟨l, hl, hB⟩ := hconn u v ⟨hes ▸ heends.1, hut⟩ ⟨hft ▸ hfends.2, hvt⟩
  have hp : IsPath (orderCx P).src (orderCx P).tgt [e, f] u v := he.append hf
  have hT : PathIn (fun x : P => x ≤ t) [e, f] := by
    apply pathIn_cons
    · obtain ⟨e, b⟩ := e
      cases b with
      | false =>
        change e.1.2 = u at hes
        change e.1.1 = t at het
        exact ⟨het ▸ le_refl t, hes ▸ hut.le⟩
      | true =>
        change e.1.1 = u at hes
        change e.1.2 = t at het
        exact ⟨hes ▸ hut.le, het ▸ le_refl t⟩
    · apply pathIn_cons
      · obtain ⟨f, b⟩ := f
        cases b with
        | false =>
          change f.1.2 = t at hfs
          change f.1.1 = v at hft
          exact ⟨hft ▸ hvt.le, hfs ▸ le_refl t⟩
        | true =>
          change f.1.1 = t at hfs
          change f.1.2 = v at hft
          exact ⟨hfs ▸ le_refl t, hft ▸ hvt.le⟩
      · exact pathIn_nil _
  refine ⟨l, hl, pathIn_mono (fun _ hx => ⟨hx.1, hx.2.ne⟩) hB, ?_⟩
  apply Davis.htpy_of_loop_nil hp hl
  exact htpy_nil_of_pathIn_le_top (A := fun x : P => x ≤ t) (le_refl t)
    (fun _ h => h) hut.le (hp.append (isPath_revPath hl))
    (pathIn_append hT (pathIn_revPath (pathIn_mono (fun _ hx => hx.2.le) hB)))

theorem germ_ends_iff {B : P → Prop} (e : (orderCx P).E × Bool) :
    (B e.1.1.1 ∧ B e.1.1.2) ↔
      (B (germSrc (orderCx P).src (orderCx P).tgt e) ∧
        B (germTgt (orderCx P).src (orderCx P).tgt e)) := by
  obtain ⟨e, b⟩ := e
  cases b <;> simp only [germSrc, germTgt, Bool.false_eq_true, if_false, if_true]
  · exact and_comm
  · rfl

/-- A nondegenerate path with endpoints away from a maximal cell has a homotopic
representative avoiding that cell. -/
theorem maximal_path_representative_nondegenerate {C : P → Prop} {t : P}
    (hmax : ∀ x, C x → t ≤ x → x = t)
    (hconn : ConnectedIn (fun x => C x ∧ x < t))
    (p : List ((orderCx P).E × Bool)) {a b : P}
    (ha : C a ∧ a ≠ t) (hb : C b ∧ b ≠ t)
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b) (hC : PathIn C p)
    (hnd : ∀ e ∈ p, germSrc (orderCx P).src (orderCx P).tgt e ≠
      germTgt (orderCx P).src (orderCx P).tgt e) :
    ∃ l, IsPath (orderCx P).src (orderCx P).tgt l a b ∧
      PathIn (fun x => C x ∧ x ≠ t) l ∧ Htpy (orderCx P) a b p l := by
  induction p using List.twoStepInduction generalizing a with
  | nil => exact ⟨[], hp, pathIn_nil _, Htpy.refl _⟩
  | singleton e =>
    refine ⟨[e], hp, pathIn_cons ?_ (pathIn_nil _), Htpy.refl _⟩
    apply (germ_ends_iff (B := fun x => C x ∧ x ≠ t) e).mpr
    exact ⟨hp.1 ▸ ha, hp.2.symm ▸ hb⟩
  | cons_cons e f p ih ihTail =>
    have heC := (pathIn_of_cons hC).1
    have htail := (pathIn_of_cons hC).2
    have hfC := (pathIn_of_cons htail).1
    have hrest := (pathIn_of_cons htail).2
    have he : IsPath (orderCx P).src (orderCx P).tgt [e] a
        (germTgt (orderCx P).src (orderCx P).tgt e) := ⟨hp.1, rfl⟩
    have hwC := (germ_ends heC).2
    by_cases hw : germTgt (orderCx P).src (orderCx P).tgt e = t
    · have hf : IsPath (orderCx P).src (orderCx P).tgt [f] t
          (germTgt (orderCx P).src (orderCx P).tgt f) := ⟨hw ▸ hp.2.1, rfl⟩
      have hv : germTgt (orderCx P).src (orderCx P).tgt f ≠ t := by
        intro hvt
        exact hnd f (by simp) (by rw (config := { transparency := .default }) [← hf.1, hvt])
      have hpair : PathIn C [e, f] := pathIn_cons heC (pathIn_cons hfC (pathIn_nil _))
      obtain ⟨l, hl, hB, hh⟩ := maximal_detour_germs hmax hconn e f
        (hw ▸ he) hf hpair ha.2 hv
      obtain ⟨r, hr, hrB, hhr⟩ := ih ⟨(germ_ends hfC).2, hv⟩ hp.2.2 hrest
        (fun g hg => hnd g (by simp [hg]))
      exact ⟨l ++ r, hl.append hr, pathIn_append hB hrB,
        Htpy.append_congr (he.append (by simpa only [hw] using hf)) hp.2.2 hh hhr⟩
    · obtain ⟨r, hr, hrB, hh⟩ := ihTail f ⟨hwC, hw⟩ hp.2 htail
        (fun g hg => hnd g (List.mem_cons_of_mem e hg))
      have heB : PathIn (fun x => C x ∧ x ≠ t) [e] := by
        apply pathIn_cons
        · exact (germ_ends_iff (B := fun x => C x ∧ x ≠ t) e).mpr ⟨hp.1 ▸ ha, ⟨hwC, hw⟩⟩
        · exact pathIn_nil _
      exact ⟨[e] ++ r, he.append hr, pathIn_append heB hrB,
        Htpy.append_congr he hp.2 (Htpy.refl _) hh⟩

theorem normalizeOrdGerm_properties {C : P → Prop} (e : (orderCx P).E × Bool)
    (hC : C e.1.1.1 ∧ C e.1.1.2) :
    PathIn C (mapPath (strictOrderIncl P) (normalizeOrdGerm e)) ∧
      ∀ g ∈ mapPath (strictOrderIncl P) (normalizeOrdGerm e),
        germSrc (orderCx P).src (orderCx P).tgt g ≠
          germTgt (orderCx P).src (orderCx P).tgt g := by
  classical
  unfold normalizeOrdGerm
  split_ifs with h
  · exact ⟨pathIn_nil _, by simp [mapPath]⟩
  · constructor
    · exact pathIn_cons hC (pathIn_nil _)
    · intro g hg
      have hg' : g = (⟨e.1.1, e.1.2⟩, e.2) := by simpa [mapPath, strictOrderIncl] using hg
      subst g
      obtain ⟨e, b⟩ := e
      cases b with
      | false => exact Ne.symm h
      | true => exact h

theorem normalizeOrdPath_properties {C : P → Prop}
    (p : List ((orderCx P).E × Bool)) (hC : PathIn C p) :
    PathIn C (mapPath (strictOrderIncl P) (normalizeOrdPath p)) ∧
      ∀ g ∈ mapPath (strictOrderIncl P) (normalizeOrdPath p),
        germSrc (orderCx P).src (orderCx P).tgt g ≠
          germTgt (orderCx P).src (orderCx P).tgt g := by
  induction p with
  | nil => exact ⟨pathIn_nil _, by simp [normalizeOrdPath, mapPath]⟩
  | cons e p ih =>
    have he := normalizeOrdGerm_properties e (pathIn_of_cons hC).1
    have hp := ih (pathIn_of_cons hC).2
    change PathIn C (mapPath (strictOrderIncl P) (normalizeOrdGerm e ++ normalizeOrdPath p)) ∧ _
    rw (config := { transparency := .default }) [mapPath_append]
    refine ⟨pathIn_append he.1 hp.1, ?_⟩
    intro g hg
    have hg' : g ∈ mapPath (strictOrderIncl P) (normalizeOrdGerm e) ++
        mapPath (strictOrderIncl P) (normalizeOrdPath p) := by
      simpa only [normalizeOrdPath, List.flatMap_cons, mapPath_append] using hg
    exact (List.mem_append.mp hg').elim (he.2 g) (hp.2 g)

/-- Complete maximal-cell path replacement, with no nondegeneracy assumption. -/
theorem maximal_path_representative {C : P → Prop} {t : P}
    (hmax : ∀ x, C x → t ≤ x → x = t)
    (hconn : ConnectedIn (fun x => C x ∧ x < t))
    (p : List ((orderCx P).E × Bool)) {a b : P}
    (ha : C a ∧ a ≠ t) (hb : C b ∧ b ≠ t)
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b) (hC : PathIn C p) :
    ∃ l, IsPath (orderCx P).src (orderCx P).tgt l a b ∧
      PathIn (fun x => C x ∧ x ≠ t) l ∧ Htpy (orderCx P) a b p l := by
  have hn := normalizeOrdPath_properties p hC
  have hpath := isPath_mapPath (strictOrderIncl P) (normalizeOrdPath_isPath hp)
  obtain ⟨l, hl, hB, hh⟩ := maximal_path_representative_nondegenerate hmax hconn
    _ ha hb hpath hn.1 hn.2
  exact ⟨l, hl, hB, (normalizeOrdPath_htpy hp).symm.trans hh⟩

end FiniteChains.Comb
