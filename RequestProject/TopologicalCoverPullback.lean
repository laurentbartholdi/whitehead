import RequestProject.TopologicalCoverPi2

/-! The concrete topological pullback of a covering map. Its covering
charts and deck homeomorphisms are constructed from those of the given
cover, with no connectedness premise on the pullback. -/

noncomputable section
namespace Whitehead
open scoped Topology Classical

variable {X Y D : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace D]

def CoverPullback (f : C(X, Y)) (p : C(D, Y)) :=
  {z : X × D // f z.1 = p z.2}

instance (f : C(X, Y)) (p : C(D, Y)) : TopologicalSpace (CoverPullback f p) :=
  inferInstanceAs (TopologicalSpace {z : X × D // f z.1 = p z.2})

def coverPullbackProjection (f : C(X, Y)) (p : C(D, Y)) : C(CoverPullback f p, X) :=
  ⟨fun z => z.val.1, continuous_fst.comp continuous_subtype_val⟩

def coverPullbackMap (f : C(X, Y)) (p : C(D, Y)) : C(CoverPullback f p, D) :=
  ⟨fun z => z.val.2, continuous_snd.comp continuous_subtype_val⟩

theorem coverPullback_square (f : C(X, Y)) (p : C(D, Y)) :
    f.comp (coverPullbackProjection f p) = p.comp (coverPullbackMap f p) := by
  apply ContinuousMap.ext
  exact fun z => z.property

private theorem coveringChart_inverse_projection {F : Type} [TopologicalSpace F]
    (p : C(D, Y)) (U : Set Y) (e : p ⁻¹' U ≃ₜ U × F)
    (he : ∀ d, (e d).1.val = p d.val) (u : U) (i : F) :
    p (e.symm (u, i)).val = u.val :=
  (he (e.symm (u, i))).symm.trans
    (congrArg (fun w : U × F => w.1.val) (e.apply_symm_apply (u, i)))

private def coverPullbackLocalChart {F : Type} [TopologicalSpace F]
    (f : C(X, Y)) (p : C(D, Y)) (U : Set Y) (e : p ⁻¹' U ≃ₜ U × F)
    (he : ∀ d, (e d).1.val = p d.val) :
    (coverPullbackProjection f p) ⁻¹' (f ⁻¹' U) ≃ₜ (f ⁻¹' U) × F where
  toFun z := (⟨z.val.val.1, z.property⟩,
    (e ⟨z.val.val.2, by
      change p z.val.val.2 ∈ U
      rw [← z.val.property]
      exact z.property⟩).2)
  invFun w := ⟨⟨(w.1.val, (e.symm (⟨f w.1.val, w.1.property⟩, w.2)).val),
    (coveringChart_inverse_projection p U e he ⟨f w.1.val, w.1.property⟩ w.2).symm⟩,
    w.1.property⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    refine Prod.ext rfl ?_
    let d : p ⁻¹' U := ⟨z.val.val.2, by
      change p z.val.val.2 ∈ U
      rw [← z.val.property]
      exact z.property⟩
    have hd : (⟨f z.val.val.1, z.property⟩, (e d).2) = e d := by
      refine Prod.ext ?_ rfl
      apply Subtype.ext
      exact z.val.property.trans (he d).symm
    change (e.symm (⟨f z.val.val.1, z.property⟩, (e d).2)).val = d.val
    rw [hd, e.symm_apply_apply]
  right_inv w := by
    refine Prod.ext rfl ?_
    exact congrArg (fun v : U × F => v.2)
      (e.apply_symm_apply (⟨f w.1.val, w.1.property⟩, w.2))
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem coverPullbackProjection_isCoveringMap (f : C(X, Y)) (p : C(D, Y))
    (hp : IsCoveringMap p) : IsCoveringMap (coverPullbackProjection f p) := by
  intro x
  obtain ⟨hdisc, U, hx, hU, _, e, he⟩ := hp (f x)
  have h : IsEvenlyCovered (coverPullbackProjection f p) x (p ⁻¹' {f x}) := by
    refine ⟨hdisc, f ⁻¹' U, hx, hU.preimage f.continuous,
      (hU.preimage f.continuous).preimage (coverPullbackProjection f p).continuous,
      coverPullbackLocalChart f p U e he, ?_⟩
    exact fun _ => rfl
  exact h.to_isEvenlyCovered_preimage

theorem coverPullbackProjection_surjective (f : C(X, Y)) (p : C(D, Y))
    (hp : Function.Surjective p) : Function.Surjective (coverPullbackProjection f p) := by
  intro x
  obtain ⟨d, hd⟩ := hp (f x)
  exact ⟨⟨(x, d), hd.symm⟩, rfl⟩

def coverPullbackDeck (f : C(X, Y)) (p : C(D, Y))
    (h : D ≃ₜ D) (hh : ∀ d, p (h d) = p d) : CoverPullback f p ≃ₜ CoverPullback f p where
  toFun z := ⟨(z.val.1, h z.val.2), z.property.trans (hh z.val.2).symm⟩
  invFun z := ⟨(z.val.1, h.symm z.val.2), z.property.trans (by
    have he := hh (h.symm z.val.2)
    rw [h.apply_symm_apply] at he
    exact he)⟩
  left_inv z := by
    apply Subtype.ext
    exact Prod.ext rfl (h.symm_apply_apply z.val.2)
  right_inv z := by
    apply Subtype.ext
    exact Prod.ext rfl (h.apply_symm_apply z.val.2)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem coverPullbackProjection_regular (f : C(X, Y)) (p : C(D, Y))
    (hp : Regular p) : Regular (coverPullbackProjection f p) := by
  intro a b hab
  have hpab : p a.val.2 = p b.val.2 :=
    a.property.symm.trans ((congrArg f hab).trans b.property)
  obtain ⟨h, hh, he⟩ := hp a.val.2 b.val.2 hpab
  refine ⟨coverPullbackDeck f p h hh, fun _ => rfl, ?_⟩
  apply Subtype.ext
  exact Prod.ext hab he

def coverPullbackIdentity (p : C(D, Y)) : CoverPullback (ContinuousMap.id Y) p ≃ₜ D where
  toFun := coverPullbackMap (ContinuousMap.id Y) p
  invFun d := ⟨(p d, d), rfl⟩
  left_inv z := by
    apply Subtype.ext
    exact Prod.ext z.property.symm rfl
  right_inv _ := rfl
  continuous_toFun := (coverPullbackMap (ContinuousMap.id Y) p).continuous
  continuous_invFun := (p.continuous.prodMk continuous_id).subtype_mk _

def coverPullbackComposition {Z : Type} [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (p : C(D, Z)) :
    CoverPullback f (coverPullbackProjection g p) ≃ₜ CoverPullback (g.comp f) p where
  toFun z := ⟨(z.val.1, z.val.2.val.2),
    (congrArg g z.property).trans z.val.2.property⟩
  invFun z := ⟨(z.val.1, ⟨(f z.val.1, z.val.2), z.property⟩), rfl⟩
  left_inv z := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    apply Subtype.ext
    exact Prod.ext z.property rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem coverPullbackComposition_map {Z : Type} [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (p : C(D, Z))
    (z : CoverPullback f (coverPullbackProjection g p)) :
    coverPullbackMap (g.comp f) p (coverPullbackComposition f g p z) =
      coverPullbackMap g p (coverPullbackMap f (coverPullbackProjection g p) z) := rfl

end Whitehead
