import RequestProject.ChamberQuotientDeckGeneration
import RequestProject.CoveringHomUniqueness

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

noncomputable def qBaseChosenInclusion {a : Qpos A X att} (b : QLiftedBase a)
    (hc : IsConnected (orderCx (Qpos A X att))) (hx : IsConnected (orderCx X)) :
    Hom (uCover (orderCx X) (qBaseCoverEnd (X := X) a b))
      (uCover (orderCx (Qpos A X att)) a) :=
  uOrderHom.comp ((ordSubposetIncl {p : UOrder (Qpos A X att) a | InQBase (uOrderEnd p)}).comp
    ((ordSubposetIncl {p : QLiftedBase a | Reach (orderCx (QLiftedBase a)) b p}).comp
      (qBaseComponentUniversalHom a hc hx b)))

omit [Fintype V] in
/-- The fixed-component map in cycle generation is a genuine cellular homomorphism. -/
theorem qBaseDeckCoverFaceMap_one {a : Qpos A X att} (b : QLiftedBase a)
    (hc : IsConnected (orderCx (Qpos A X att))) (hx : IsConnected (orderCx X))
    (t : UF (orderCx X) (qBaseCoverEnd (X := X) a b)) :
    qBaseDeckCoverFaceMap b 1 hc hx t = (qBaseChosenInclusion b hc hx).onF t := by
  apply Subtype.ext
  apply Prod.ext
  · exact deckV_one _
  · apply Subtype.ext
    change (uOrderEnd (deckV 1 _), uOrderEnd (deckV 1 _), uOrderEnd (deckV 1 _)) = _
    simp only [deckV_one]
    rfl

omit [Fintype V] in
theorem qBaseChosenInclusion_vertex_projection {a : Qpos A X att} (b : QLiftedBase a)
    (hc : IsConnected (orderCx (Qpos A X att))) (hx : IsConnected (orderCx X))
    (v : UV (orderCx X) (qBaseCoverEnd (X := X) a b)) :
    endV ((qBaseChosenInclusion b hc hx).onV v) = qNew (X := X) (A := A) (att := att) (endV v) := by
  have h := onV_coverV (qBaseComponentProjection_isCovering a hc hx b)
    (d₀ := qBaseComponentRoot a b) rfl v
  have hs := qBaseCoverEnd_spec (X := X) a
    ((qBaseComponentUniversalHom a hc hx b).onV v).1
  change qNew (X := X) (A := A) (att := att) (qBaseCoverEnd (X := X) a
    ((qBaseComponentUniversalHom a hc hx b).onV v).1) = _ at hs
  change qBaseCoverEnd (X := X) a
    ((qBaseComponentUniversalHom a hc hx b).onV v).1 = endV v at h
  exact hs.symm.trans (congrArg (qNew (X := X) (A := A) (att := att)) h)

omit [Fintype V] in
theorem qBaseChosenInclusion_base {a : Qpos A X att} (b : QLiftedBase a)
    (hc : IsConnected (orderCx (Qpos A X att))) (hx : IsConnected (orderCx X)) :
    (qBaseChosenInclusion b hc hx).onV
      (UV.base (orderCx X) (qBaseCoverEnd (X := X) a b)) = b.1 := by
  change (coverV (qBaseComponentProjection_isCovering a hc hx b)
    (d₀ := qBaseComponentRoot a b) rfl
      (UV.base (orderCx X) (qBaseCoverEnd (X := X) a b))).1.1 = b.1
  exact congrArg (fun w : QBaseComponent a b => w.1.1)
    (coverV_base (qBaseComponentProjection_isCovering a hc hx b)
      (d₀ := qBaseComponentRoot a b) rfl)

omit [Fintype V] in
theorem qBaseChosenInclusion_edge_projection {a : Qpos A X att} (b : QLiftedBase a)
    (hc : IsConnected (orderCx (Qpos A X att))) (hx : IsConnected (orderCx X))
    (e : UE (orderCx X) (qBaseCoverEnd (X := X) a b)) :
    ((qBaseChosenInclusion b hc hx).onE e).1.2 =
      (orderCxMap (qNew (X := X) (A := A) (att := att)) qNew_monotone).onE e.1.2 := by
  apply Subtype.ext
  apply Prod.ext
  · have h := congrArg endV ((qBaseChosenInclusion b hc hx).src_onE e)
    change endV ((qBaseChosenInclusion b hc hx).onE e).1.1 =
      endV ((qBaseChosenInclusion b hc hx).onV e.1.1) at h
    rw (config := { transparency := .default }) [qBaseChosenInclusion_vertex_projection] at h
    exact (((qBaseChosenInclusion b hc hx).onE e).2).symm.trans
      (h.trans (congrArg (qNew (X := X) (A := A) (att := att)) e.2))
  · have h := congrArg endV ((qBaseChosenInclusion b hc hx).tgt_onE e)
    rw (config := { transparency := .default }) [qBaseChosenInclusion_vertex_projection] at h
    change endV (extend (_, true) _) = _ at h
    rw (config := { transparency := .default }) [endV_extend ((qBaseChosenInclusion b hc hx).onE e).2] at h
    change _ = qNew (X := X) (A := A) (att := att)
      (endV (extend (e.1.2, true) e.1.1)) at h
    rw (config := { transparency := .default }) [endV_extend e.2] at h
    exact h

omit [Fintype V] in
theorem qBaseChosenInclusion_onV_unique {a : Qpos A X att} (b : QLiftedBase a)
    (hc : IsConnected (orderCx (Qpos A X att))) (hx : IsConnected (orderCx X))
    (f : Hom (uCover (orderCx X) (qBaseCoverEnd (X := X) a b))
      (uCover (orderCx (Qpos A X att)) a))
    (hf : f.onV (UV.base (orderCx X) (qBaseCoverEnd (X := X) a b)) = b.1)
    (he : ∀ e, (f.onE e).1.2 =
      (orderCxMap (qNew (X := X) (A := A) (att := att)) qNew_monotone).onE e.1.2) :
    ∀ v, (qBaseChosenInclusion b hc hx).onV v = f.onV v := by
  apply coveringHom_onV_unique (univProj (orderCx (Qpos A X att)) a)
    (isCovering_univProj hc) (qBaseChosenInclusion b hc hx) f
    isConnected_univCover (UV.base (orderCx X) (qBaseCoverEnd (X := X) a b))
  · exact (qBaseChosenInclusion_base b hc hx).trans hf.symm
  · intro e
    exact (qBaseChosenInclusion_edge_projection b hc hx e).trans (he e).symm

omit [Fintype V] in
theorem qBaseChosenInclusion_face_projection {a : Qpos A X att} (b : QLiftedBase a)
    (hc : IsConnected (orderCx (Qpos A X att))) (hx : IsConnected (orderCx X))
    (t : UF (orderCx X) (qBaseCoverEnd (X := X) a b)) :
    ((qBaseChosenInclusion b hc hx).onF t).1.2 =
      (orderCxMap (qNew (X := X) (A := A) (att := att)) qNew_monotone).onF t.1.2 := by
  let k : OrdTri (QBaseComponent a b) := (qBaseComponentUniversalHom a hc hx b).onF t
  have hk : (qBaseComponentProjection a hc hx b).onF k = t.1.2 :=
    onF_coverF (qBaseComponentProjection_isCovering a hc hx b)
      (d₀ := qBaseComponentRoot a b) rfl t
  apply Subtype.ext
  apply Prod.ext
  · have h := congrArg (fun t : OrdTri X => t.1.1) hk
    exact (qBaseCoverEnd_spec (X := X) a k.1.1.1).symm.trans
      (congrArg (qNew (X := X) (A := A) (att := att)) h)
  · apply Prod.ext
    · have h := congrArg (fun t : OrdTri X => t.1.2.1) hk
      exact (qBaseCoverEnd_spec (X := X) a k.1.2.1.1).symm.trans
        (congrArg (qNew (X := X) (A := A) (att := att)) h)
    · have h := congrArg (fun t : OrdTri X => t.1.2.2) hk
      exact (qBaseCoverEnd_spec (X := X) a k.1.2.2.1).symm.trans
        (congrArg (qNew (X := X) (A := A) (att := att)) h)

omit [Fintype V] in
theorem qBaseChosenInclusion_onF_unique {a : Qpos A X att} (b : QLiftedBase a)
    (hc : IsConnected (orderCx (Qpos A X att))) (hx : IsConnected (orderCx X))
    (f : Hom (uCover (orderCx X) (qBaseCoverEnd (X := X) a b))
      (uCover (orderCx (Qpos A X att)) a))
    (hf : f.onV (UV.base (orderCx X) (qBaseCoverEnd (X := X) a b)) = b.1)
    (he : ∀ e, (f.onE e).1.2 =
      (orderCxMap (qNew (X := X) (A := A) (att := att)) qNew_monotone).onE e.1.2)
    (ht : ∀ t, (f.onF t).1.2 =
      (orderCxMap (qNew (X := X) (A := A) (att := att)) qNew_monotone).onF t.1.2) :
    ∀ t, (qBaseChosenInclusion b hc hx).onF t = f.onF t := by
  intro t
  apply Subtype.ext
  apply Prod.ext
  · exact ((qBaseChosenInclusion b hc hx).base_onF t).trans
      ((qBaseChosenInclusion_onV_unique b hc hx f hf he _).trans (f.base_onF t).symm)
  · exact (qBaseChosenInclusion_face_projection b hc hx t).trans (ht t).symm

end FiniteChains.Davis
