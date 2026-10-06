module

public import RequestProject.PosetCoverPullback
public import RequestProject.StrictOrderComplex
public import RequestProject.PosetCoverUpTransform
public import RequestProject.ComponentComplex

@[expose] public section

/-! Actual cellular maps into a pulled-back ordered cover.

-/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P Q R : Type u} [PartialOrder P] [PartialOrder Q] [PartialOrder R]
  (f : P → Q) (hf : IsPosetCover f) (g : R → Q) (hg : Monotone g)

noncomputable def strictPullbackOriginal :
    Hom (strictOrderCx (PosetCoverPullback f g)) (orderCx P) :=
  (orderCxMap (posetPullbackOriginal f g) (posetPullbackOriginal_monotone f g)).comp
    (strictOrderIncl _)

noncomputable def strictPullbackProjection :
    Hom (strictOrderCx (PosetCoverPullback f g)) (strictOrderCx R) :=
  strictOrderCxMap (posetPullbackProjection f g) (hf.pullback g hg).strictMono

omit [PartialOrder Q] in
theorem pullback_lt {a b : PosetCoverPullback f g}
    (hp : a.1.1 ≤ b.1.1) (hr : a.1.2 < b.1.2) : a < b := by
  exact lt_iff_le_not_ge.mpr ⟨⟨hp, hr.le⟩, fun h => (not_le_of_gt hr) h.2⟩

variable {K : Complex2.{u}} (r : Hom K (orderCx P)) (s : Hom K (strictOrderCx R))
  (h : (orderCxMap f hf.mono).comp r =
    (orderCxMap g hg).comp ((strictOrderIncl R).comp s))

noncomputable def strictPullbackVertex (a : K.V) : PosetCoverPullback f g :=
  ⟨(r.onV a, s.onV a), congrArg (fun k : Hom K (orderCx Q) => k.onV a) h⟩

noncomputable def strictPullbackEdge (e : K.E) : StrictOrdEdge (PosetCoverPullback f g) := by
  have he := congrArg (fun k : Hom K (orderCx Q) => k.onE e) h
  let a : PosetCoverPullback f g :=
    ⟨((r.onE e).1.1, (s.onE e).1.1), congrArg (fun x : OrdEdge Q => x.1.1) he⟩
  let b : PosetCoverPullback f g :=
    ⟨((r.onE e).1.2, (s.onE e).1.2), congrArg (fun x : OrdEdge Q => x.1.2) he⟩
  exact ⟨(a, b), pullback_lt f g (r.onE e).2 (s.onE e).2⟩

noncomputable def strictPullbackFace (t : K.F) : StrictOrdTri (PosetCoverPullback f g) := by
  have ht := congrArg (fun k : Hom K (orderCx Q) => k.onF t) h
  let a : PosetCoverPullback f g :=
    ⟨((r.onF t).1.1, (s.onF t).1.1), congrArg (fun x : OrdTri Q => x.1.1) ht⟩
  let b : PosetCoverPullback f g :=
    ⟨((r.onF t).1.2.1, (s.onF t).1.2.1), congrArg (fun x : OrdTri Q => x.1.2.1) ht⟩
  let c : PosetCoverPullback f g :=
    ⟨((r.onF t).1.2.2, (s.onF t).1.2.2), congrArg (fun x : OrdTri Q => x.1.2.2) ht⟩
  exact ⟨(a, b, c), pullback_lt f g (r.onF t).2.1 (s.onF t).2.1,
    pullback_lt f g (r.onF t).2.2 (s.onF t).2.2⟩

theorem strictPullbackEdge_first (e : K.E) :
    (strictPullbackOriginal f g).onE (strictPullbackEdge f hf g hg r s h e) = r.onE e := rfl

theorem strictPullbackEdge_second (e : K.E) :
    (strictPullbackProjection f hf g hg).onE (strictPullbackEdge f hf g hg r s h e) =
      s.onE e := rfl

theorem strictPullbackFace_first (t : K.F) :
    (strictPullbackOriginal f g).onF (strictPullbackFace f hf g hg r s h t) = r.onF t := rfl

theorem strictPullbackFace_second (t : K.F) :
    (strictPullbackProjection f hf g hg).onF (strictPullbackFace f hf g hg r s h t) =
      s.onF t := rfl

theorem list_eq_of_two_maps {A B C : Type*} (p : A → B) (q : A → C)
    (hi : ∀ x y, p x = p y → q x = q y → x = y)
    (l m : List A) (hp : l.map p = m.map p) (hq : l.map q = m.map q) : l = m := by
  induction l generalizing m with
  | nil => exact (List.map_eq_nil_iff.mp hp.symm).symm
  | cons x l ih =>
      cases m with
      | nil => cases hp
      | cons y m =>
          obtain ⟨hp0, hp1⟩ := List.cons.inj hp
          obtain ⟨hq0, hq1⟩ := List.cons.inj hq
          exact congrArg₂ List.cons (hi x y hp0 hq0) (ih m hp1 hq1)

theorem pullback_germ_ext
    (x y : (strictOrderCx (PosetCoverPullback f g)).E × Bool)
    (hp : ((strictPullbackOriginal f g).onE x.1, x.2) =
      ((strictPullbackOriginal f g).onE y.1, y.2))
    (hq : ((strictPullbackProjection f hf g hg).onE x.1, x.2) =
      ((strictPullbackProjection f hf g hg).onE y.1, y.2)) : x = y := by
  have hb : x.2 = y.2 := congrArg (fun e : OrdEdge P × Bool => e.2) hp
  refine Prod.ext ?_ hb
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact Prod.ext (congrArg (fun e : OrdEdge P × Bool => e.1.1.1) hp)
      (congrArg (fun e : StrictOrdEdge R × Bool => e.1.1.1) hq)
  · apply Subtype.ext
    exact Prod.ext (congrArg (fun e : OrdEdge P × Bool => e.1.1.2) hp)
      (congrArg (fun e : StrictOrdEdge R × Bool => e.1.1.2) hq)

/-- Two genuinely commuting cellular maps produce a cellular map into the
actual ordered fibre product. Its attaching paths follow from both projections. -/
noncomputable def strictOrderPullbackHom :
    Hom K (strictOrderCx (PosetCoverPullback f g)) where
  onV := strictPullbackVertex f hf g hg r s h
  onE := strictPullbackEdge f hf g hg r s h
  onF := strictPullbackFace f hf g hg r s h
  src_onE e := by
    apply Subtype.ext
    exact Prod.ext (r.src_onE e) (s.src_onE e)
  tgt_onE e := by
    apply Subtype.ext
    exact Prod.ext (r.tgt_onE e) (s.tgt_onE e)
  base_onF t := by
    apply Subtype.ext
    exact Prod.ext (r.base_onF t) (s.base_onF t)
  att_onF t := by
    apply list_eq_of_two_maps
      (fun e => ((strictPullbackOriginal f g).onE e.1, e.2))
      (fun e => ((strictPullbackProjection f hf g hg).onE e.1, e.2))
      (pullback_germ_ext f hf g hg)
    · rw [← (strictPullbackOriginal f g).att_onF]
      rw [strictPullbackFace_first]
      simpa only [List.map_map, Function.comp_def, strictPullbackEdge_first]
        using r.att_onF t
    · rw [← (strictPullbackProjection f hf g hg).att_onF]
      rw [strictPullbackFace_second]
      simpa only [List.map_map, Function.comp_def, strictPullbackEdge_second]
        using s.att_onF t

theorem strictOrderPullbackHom_first :
    (strictPullbackOriginal f g).comp (strictOrderPullbackHom f hf g hg r s h) = r := by
  apply Hom.ext'
  · rfl
  · rfl
  · rfl

theorem strictOrderPullbackHom_second :
    (strictPullbackProjection f hf g hg).comp (strictOrderPullbackHom f hf g hg r s h) = s := by
  apply Hom.ext'
  · rfl
  · rfl
  · rfl

end FiniteChains.Comb
