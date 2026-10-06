import RequestProject.OrderCocycleCover
import RequestProject.OrderUniversalPosetConnected
import RequestProject.PosetCoverStrictEdgeLift

namespace FiniteChains.Comb.OrdCocycle
universe u
variable {P G : Type u} [PartialOrder P] [Group G] (c : OrdCocycle P G)

/-- Sheet coordinates on an actual fibre of the cocycle covering. -/
def coverFibreEquiv (p : P) : {x : c.Cover // x.point = p} ≃ G where
  toFun x := x.val.sheet
  invFun g := ⟨⟨p, g⟩, rfl⟩
  left_inv x := by
    apply Subtype.ext
    cases x with
    | mk x hx => cases x; cases hx; rfl
  right_inv _ := rfl

/-- The genuine universal-cover path class maps to its endpoint and reading. -/
def universalReading (a : P) (v : UOrder P a) : c.Cover :=
  ⟨uOrderEnd v, c.readVertex a v⟩

theorem universalReading_monotone (a : P) : Monotone (c.universalReading a) := by
  intro v w h
  obtain ⟨h, hw⟩ := h
  refine ⟨h, ?_⟩
  change c.readVertex a v * c.val (uOrderEnd v) (uOrderEnd w) = c.readVertex a w
  have he := c.readVertex_extend a (ordPos h) v rfl
  change c.readVertex a (uOrderStep v (uOrderEnd w) h) =
    c.readVertex a v * c.val (uOrderEnd v) (uOrderEnd w) at he
  rw [hw] at he
  exact he.symm

theorem universalReading_surjective (a : P) (hP : IsConnected (orderCx P))
    (hm : Function.Surjective (c.monodromy a)) :
    Function.Surjective (c.universalReading a) := by
  rintro ⟨p, g⟩
  obtain ⟨v, hv⟩ := (uOrderEnd_isPosetCover (a := a) hP).surj p
  obtain ⟨z, hz, hg⟩ := c.readVertex_fibre_surjective a hm v g
  refine ⟨z, ?_⟩
  change Cover.mk (uOrderEnd z) (c.readVertex a z) = Cover.mk p g
  rw [hg, show uOrderEnd z = p from hz.trans hv]

/-- Surjective monodromy, rather than faithful monodromy, gives a connected cover. -/
theorem cover_isConnected (a : P) (hP : IsConnected (orderCx P))
    (hm : Function.Surjective (c.monodromy a)) : IsConnected (orderCx c.Cover) := by
  intro v w
  obtain ⟨v', rfl⟩ := c.universalReading_surjective a hP hm v
  obtain ⟨w', rfl⟩ := c.universalReading_surjective a hP hm w
  obtain ⟨p, hp⟩ := uOrder_complex_isConnected (P := P) (a := a) v' w'
  exact ⟨mapPath (orderCxMap (c.universalReading a) (c.universalReading_monotone a)) p,
    isPath_mapPath _ hp⟩

theorem cover_deck_transitive (v w : c.Cover) (h : v.point = w.point) :
    ∃ e : c.Cover ≃o c.Cover,
      (∀ p, (e p).point = p.point) ∧ e v = w := by
  refine ⟨c.coverDeck (w.sheet * v.sheet⁻¹), fun _ => rfl, ?_⟩
  cases v with
  | mk vp vg =>
    cases w with
    | mk wp wg =>
      dsimp only at h
      subst wp
      simp [coverDeck, mul_assoc]

/-- An actual lifted strict incidence records precisely multiplication by its cocycle. -/
theorem strictEdge_sheet (e : StrictOrdEdge c.Cover) :
    e.val.1.sheet * c.val e.val.1.point e.val.2.point = e.val.2.sheet := e.property.le.2

theorem strictEdgeLiftFrom_sheet (e : StrictOrdEdge P) (v : c.Cover)
    (hv : v.point = e.val.1) :
    ((c.coverProjection_isPosetCover).strictEdgeLiftFrom e v hv).val.2.sheet =
      v.sheet * c.val e.val.1 e.val.2 := by
  let r := (c.coverProjection_isPosetCover).strictEdgeLiftFrom e v hv
  have ht := congrArg (fun z : StrictOrdEdge P => z.val.2)
    ((c.coverProjection_isPosetCover).strictEdgeLiftFrom_projection e v hv)
  change r.val.2.point = e.val.2 at ht
  have he := (c.strictEdge_sheet r).symm
  change r.val.2.sheet = v.sheet * c.val v.point r.val.2.point at he
  rw [hv, ht] at he
  exact he

theorem strictEdgeLiftTo_sheet (e : StrictOrdEdge P) (v : c.Cover)
    (hv : v.point = e.val.2) :
    ((c.coverProjection_isPosetCover).strictEdgeLiftTo e v hv).val.1.sheet =
      v.sheet * (c.val e.val.1 e.val.2)⁻¹ := by
  let r := (c.coverProjection_isPosetCover).strictEdgeLiftTo e v hv
  have hs := congrArg (fun z : StrictOrdEdge P => z.val.1)
    ((c.coverProjection_isPosetCover).strictEdgeLiftTo_projection e v hv)
  change r.val.1.point = e.val.1 at hs
  have he := c.strictEdge_sheet r
  change r.val.1.sheet * c.val r.val.1.point v.point = v.sheet at he
  rw [hs, hv] at he
  rw [← he]
  simp only [mul_assoc, mul_inv_cancel, mul_one]
  rfl

end FiniteChains.Comb.OrdCocycle
