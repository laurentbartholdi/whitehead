module

public import RequestProject.OrderUniversalPosetCover

@[expose] public section

/-! Actual edge and triangle coordinates of the universal-cover order complex. -/
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

def uOrderEdge (e : OrdEdge (UOrder P a)) : UE (orderCx P) a :=
  ⟨(e.1.1, ⟨(uOrderEnd e.1.1, uOrderEnd e.1.2), uOrderEnd_monotone e.2⟩), rfl⟩

def uOrderFace (t : OrdTri (UOrder P a)) : UF (orderCx P) a :=
  ⟨(t.1.1, ⟨(uOrderEnd t.1.1, uOrderEnd t.1.2.1, uOrderEnd t.1.2.2),
    uOrderEnd_monotone t.2.1, uOrderEnd_monotone t.2.2⟩), rfl⟩

theorem uOrder_up_injective {v w z : UOrder P a} (hw : v ≤ w) (hz : v ≤ z)
    (he : uOrderEnd w = uOrderEnd z) : w = z := by
  obtain ⟨hvw, ew⟩ := hw
  obtain ⟨hvz, ez⟩ := hz
  exact ew.symm.trans ((uOrderStep_eq_of_target_eq v hvw hvz he).trans ez)

theorem uOrderEdge_injective : Function.Injective (uOrderEdge (P := P) (a := a)) := by
  intro e f h
  have hroot : e.1.1 = f.1.1 := congrArg (fun g : UE (orderCx P) a => g.1.1) h
  have hend : uOrderEnd e.1.2 = uOrderEnd f.1.2 :=
    congrArg (fun g : UE (orderCx P) a => g.1.2.1.2) h
  have ht : e.1.2 = f.1.2 := uOrder_up_injective e.2 (hroot ▸ f.2) hend
  exact Subtype.ext (Prod.ext hroot ht)

theorem uOrderFace_injective : Function.Injective (uOrderFace (P := P) (a := a)) := by
  intro t s h
  have hroot : t.1.1 = s.1.1 := congrArg (fun g : UF (orderCx P) a => g.1.1) h
  have hmid : uOrderEnd t.1.2.1 = uOrderEnd s.1.2.1 :=
    congrArg (fun g : UF (orderCx P) a => g.1.2.1.2.1) h
  have htop : uOrderEnd t.1.2.2 = uOrderEnd s.1.2.2 :=
    congrArg (fun g : UF (orderCx P) a => g.1.2.1.2.2) h
  have hm : t.1.2.1 = s.1.2.1 := uOrder_up_injective t.2.1 (hroot ▸ s.2.1) hmid
  have ht : t.1.2.2 = s.1.2.2 :=
    uOrder_up_injective (t.2.1.trans t.2.2) (hroot ▸ s.2.1.trans s.2.2) htop
  exact Subtype.ext (Prod.ext hroot (Prod.ext hm ht))

theorem uOrderEdge_surjective : Function.Surjective (uOrderEdge (P := P) (a := a)) := by
  rintro ⟨⟨v, e⟩, hv⟩
  have hv' : uOrderEnd (v : UOrder P a) = e.1.1 := hv
  let h : uOrderEnd (v : UOrder P a) ≤ e.1.2 := hv'.le.trans e.2
  let w := uOrderStep (v : UOrder P a) e.1.2 h
  refine ⟨⟨(v, w), uOrderStep_le v _ h⟩, ?_⟩
  exact Subtype.ext (Prod.ext rfl
    (Subtype.ext (Prod.ext hv (uOrderStep_end v _ h))))

theorem uOrderFace_surjective : Function.Surjective (uOrderFace (P := P) (a := a)) := by
  rintro ⟨⟨v, t⟩, hv⟩
  have hv' : uOrderEnd (v : UOrder P a) = t.1.1 := hv
  let h : uOrderEnd (v : UOrder P a) ≤ t.1.2.1 := hv'.le.trans t.2.1
  let w := uOrderStep (v : UOrder P a) t.1.2.1 h
  let h' : uOrderEnd w ≤ t.1.2.2 := (uOrderStep_end v _ h).le.trans t.2.2
  let z := uOrderStep w t.1.2.2 h'
  refine ⟨⟨(v, w, z), uOrderStep_le v _ h, uOrderStep_le w _ h'⟩, ?_⟩
  exact Subtype.ext (Prod.ext rfl (Subtype.ext
    (Prod.ext hv (Prod.ext (uOrderStep_end v _ h) (uOrderStep_end w _ h')))))

end FiniteChains.Comb
