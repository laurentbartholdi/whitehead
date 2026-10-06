import RequestProject.OrderPosetCovering

/-! An actual set-valued local system on a poset gives a poset covering.
The construction retains the whole fibre; no choice of group coordinates
or covering classification theorem is needed. Unverified source. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.LocalSystem
open CategoryTheory
universe u
variable {P : Type u} [PartialOrder P] (F : P ⥤ Type u)

def Cover := Σ p : P, F.obj p

instance coverPartialOrder : PartialOrder (Cover F) where
  le x y := ∃ h : x.1 ≤ y.1, F.map (homOfLE h) x.2 = y.2
  le_refl x := ⟨le_rfl, by simp⟩
  le_trans x y z hxy hyz := by
    obtain ⟨hxy, hfx⟩ := hxy
    obtain ⟨hyz, hfy⟩ := hyz
    refine ⟨hxy.trans hyz, ?_⟩
    have hh := ConcreteCategory.congr_hom (F.map_comp (homOfLE hxy) (homOfLE hyz)) x.2
    change F.map (homOfLE (hxy.trans hyz)) x.2 =
      F.map (homOfLE hyz) (F.map (homOfLE hxy) x.2) at hh
    rw [hh, hfx, hfy]
  le_antisymm x y hxy hyx := by
    rcases x with ⟨p, x⟩
    rcases y with ⟨q, y⟩
    obtain ⟨hpq, hx⟩ := hxy
    obtain ⟨hqp, _⟩ := hyx
    obtain rfl := le_antisymm hpq hqp
    have hxy : x = y := by simpa using hx
    cases hxy
    rfl

def projection : Cover F → P := Sigma.fst

theorem projection_monotone : Monotone (projection F) := fun _ _ h => h.choose

theorem projection_isPosetCover
    (hF : ∀ {p q : P} (h : p ≤ q), Function.Bijective (F.map (homOfLE h)))
    (hne : ∀ p, Nonempty (F.obj p)) : IsPosetCover (projection F) := by
  classical
  refine ⟨projection_monotone F, fun p => ⟨⟨p, Classical.choice (hne p)⟩, rfl⟩, ?_, ?_⟩
  · intro x q hxq
    refine ⟨⟨q, F.map (homOfLE hxq) x.2⟩, ⟨⟨hxq, rfl⟩, rfl⟩, ?_⟩
    rintro ⟨r, y⟩ ⟨⟨hxy, hy⟩, hr⟩
    change r = q at hr
    subst r
    exact congrArg (Sigma.mk q) hy.symm
  · intro x q hqx
    obtain ⟨v, hv⟩ := (hF hqx).2 x.2
    refine ⟨⟨q, v⟩, ⟨⟨hqx, hv⟩, rfl⟩, ?_⟩
    rintro ⟨r, y⟩ ⟨⟨hyx, hy⟩, hr⟩
    change r = q at hr
    subst r
    exact congrArg (Sigma.mk q) ((hF hqx).1 (hy.trans hv.symm))

/-- An automorphism of the actual local system is an order deck map. -/
def deckOrderIso (e : F ≅ F) : Cover F ≃o Cover F where
  toFun x := ⟨x.1, e.hom.app x.1 x.2⟩
  invFun x := ⟨x.1, e.inv.app x.1 x.2⟩
  left_inv x := by
    refine Sigma.ext rfl ?_
    exact heq_of_eq (ConcreteCategory.congr_hom (Iso.hom_inv_id_app e x.1) x.2)
  right_inv x := by
    refine Sigma.ext rfl ?_
    exact heq_of_eq (ConcreteCategory.congr_hom (Iso.inv_hom_id_app e x.1) x.2)
  map_rel_iff' := by
    intro x y
    constructor
    · rintro ⟨hxy, heq⟩
      refine ⟨hxy, ?_⟩
      apply (show Function.Injective (e.hom.app y.1) from
        (isIso_iff_bijective (e.hom.app y.1)).mp inferInstance |>.1)
      have hn := ConcreteCategory.congr_hom (e.hom.naturality (homOfLE hxy)) x.2
      exact hn.trans heq
    · rintro ⟨hxy, heq⟩
      refine ⟨hxy, ?_⟩
      have hn := ConcreteCategory.congr_hom (e.hom.naturality (homOfLE hxy)) x.2
      exact hn.symm.trans (congrArg (e.hom.app y.1) heq)

theorem deckOrderIso_projection (e : F ≅ F) (x : Cover F) :
    projection F (deckOrderIso F e x) = projection F x := rfl

end FiniteChains.Comb.LocalSystem
