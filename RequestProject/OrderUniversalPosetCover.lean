import RequestProject.OrderUniversalPoset
import RequestProject.OrderPosetCovering

/-! Unique interval lifts in the genuine path-class universal-cover order. -/
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

theorem uOrderStep_le (v : UOrder P a) (q : P) (h : uOrderEnd v ≤ q) :
    v ≤ uOrderStep v q h := by
  change UOrderLe _ _
  unfold UOrderLe
  simp only [uOrderStep_end]
  exact ⟨h, trivial⟩

theorem uOrderStep_eq_of_target_eq (v : UOrder P a) {q r : P}
    (hq : uOrderEnd v ≤ q) (hr : uOrderEnd v ≤ r) (he : q = r) :
    uOrderStep v q hq = uOrderStep v r hr := by
  subst r
  rfl

theorem uOrder_unique_up (v : UOrder P a) (q : P) (h : uOrderEnd v ≤ q) :
    ∃! w : UOrder P a, v ≤ w ∧ uOrderEnd w = q := by
  refine ⟨uOrderStep v q h, ⟨uOrderStep_le v q h, uOrderStep_end v q h⟩, ?_⟩
  intro w hw
  obtain ⟨hle, he⟩ := hw.1
  exact he.symm.trans (uOrderStep_eq_of_target_eq v hle h hw.2)

noncomputable def uOrderBack (v : UOrder P a) (q : P) (h : q ≤ uOrderEnd v) :
    UOrder P a := extend (ordNeg h) v

theorem uOrderBack_end (v : UOrder P a) (q : P) (h : q ≤ uOrderEnd v) :
    uOrderEnd (uOrderBack v q h) = q := endV_extend rfl

theorem uOrderBack_le (v : UOrder P a) (q : P) (h : q ≤ uOrderEnd v) :
    uOrderBack v q h ≤ v := by
  let hb : uOrderEnd (uOrderBack v q h) ≤ uOrderEnd v :=
    (uOrderBack_end v q h).le.trans h
  refine ⟨hb, ?_⟩
  have hg : ordPos hb = revGerm (ordNeg h) := by
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext (uOrderBack_end v q h) rfl
    · rfl
  change extend (ordPos hb) (extend (ordNeg h) v) = v
  rw [hg]
  exact extend_revGerm rfl

theorem uOrder_unique_down (v : UOrder P a) (q : P) (h : q ≤ uOrderEnd v) :
    ∃! w : UOrder P a, w ≤ v ∧ uOrderEnd w = q := by
  refine ⟨uOrderBack v q h, ⟨uOrderBack_le v q h, uOrderBack_end v q h⟩, ?_⟩
  intro w hw
  obtain ⟨hle, he⟩ := hw.1
  have hg : ordNeg hle = ordNeg h := by
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext hw.2 rfl
    · rfl
  have hr : extend (ordNeg h) (extend (ordPos hle) w) = w := by
    rw [← hg]
    exact extend_revGerm (eb := ordPos hle) rfl
  have ht := congrArg (extend (ordNeg h)) he
  exact hr.symm.trans ht

/-- The endpoint map of actual path classes is a poset covering whenever the base
order complex is connected. -/
theorem uOrderEnd_isPosetCover (hc : IsConnected (orderCx P)) :
    IsPosetCover (uOrderEnd (P := P) (a := a)) where
  mono := uOrderEnd_monotone
  surj := endV_surjective hc
  up := uOrder_unique_up
  down := uOrder_unique_down

end FiniteChains.Comb
