import RequestProject.RegularCoverActualPi2Descent

/-! Regular-cover descent for arbitrary cell sets, carrying the actual
inclusions. No finite-complement hypothesis is needed for the chain or
its spherical vanishing. Finiteness can be supplied only where wanted.
Unverified source. -/

noncomputable section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u v

theorem pushE_eq_inr_imp {D K L : Complex2.{u}} (p : Hom D K) (i : Hom D L)
    (hi : Function.Injective i.onE) (e : L.E) (w : OffE i)
    (h : pushE p i e = Sum.inr w) : e = w.val := by
  by_cases he : ∃ d, i.onE d = e
  · obtain ⟨d, rfl⟩ := he
    rw [pushE_of_mem p hi] at h
    exact (Sum.inl_ne_inr h).elim
  · rw [pushE_of_off p i ⟨e, fun d hd => he ⟨d, hd⟩⟩] at h
    exact congrArg (fun x : OffE i => x.val) (Sum.inr.inj h)

theorem pushF_eq_inr_imp {D K L : Complex2.{u}} (p : Hom D K) (i : Hom D L)
    (hi : Function.Injective i.onF) (e : L.F) (w : OffF i)
    (h : pushF p i e = Sum.inr w) : e = w.val := by
  by_cases he : ∃ d, i.onF d = e
  · obtain ⟨d, rfl⟩ := he
    rw [pushF_of_mem p hi] at h
    exact (Sum.inl_ne_inr h).elim
  · rw [pushF_of_off p i ⟨e, fun d hd => he ⟨d, hd⟩⟩] at h
    exact congrArg (fun x : OffF i => x.val) (Sum.inr.inj h)

section Proper
variable {D K L L' : Complex2.{u}} (p : Hom D K) (j : Hom D L) (j' : Hom D L')
  (k : Hom L L') (hjV : Function.Injective j.onV) (hjE : Function.Injective j.onE)
  (hj'V : Function.Injective j'.onV) (hj'E : Function.Injective j'.onE)
  (hj'F : Function.Injective j'.onF) (hkj : k.comp j = j')

theorem pushoutFunctor_not_surjective_E (hk : ¬ Function.Surjective k.onE) :
    ¬ Function.Surjective (pushoutFunctor p j j' k hjV hjE hj'V hj'E hj'F hkj).onE := by
  intro hs
  apply hk
  intro e
  by_cases he : ∃ d, j'.onE d = e
  · obtain ⟨d, hd⟩ := he
    exact ⟨j.onE d, (congrArg (fun f : Hom D L' => f.onE d) hkj).trans hd⟩
  · obtain ⟨x, hx⟩ := hs (Sum.inr (⟨e, fun d hd => he ⟨d, hd⟩⟩ : OffE j'))
    cases x with
    | inl x => exact (Sum.inl_ne_inr hx).elim
    | inr x =>
        exact ⟨x.val, pushE_eq_inr_imp p j' hj'E (k.onE x.val) _ hx⟩

theorem pushoutFunctor_not_surjective_F (hk : ¬ Function.Surjective k.onF) :
    ¬ Function.Surjective (pushoutFunctor p j j' k hjV hjE hj'V hj'E hj'F hkj).onF := by
  intro hs
  apply hk
  intro e
  by_cases he : ∃ d, j'.onF d = e
  · obtain ⟨d, hd⟩ := he
    exact ⟨j.onF d, (congrArg (fun f : Hom D L' => f.onF d) hkj).trans hd⟩
  · obtain ⟨x, hx⟩ := hs (Sum.inr (⟨e, fun d hd => he ⟨d, hd⟩⟩ : OffF j'))
    cases x with
    | inl x => exact (Sum.inl_ne_inr hx).elim
    | inr x =>
        exact ⟨x.val, pushF_eq_inr_imp p j' hj'F (k.onF x.val) _ hx⟩
end Proper

/-- Only actual map properties used in descent; no finite-cell assumptions. -/
structure RelativeCellChain (c : ℕ → Complex2.{u}) (n : ℕ) where
  inc : ∀ i, Hom (c i) (c (i + 1))
  incV : ∀ i, Function.Injective (inc i).onV
  incE : ∀ i, Function.Injective (inc i).onE
  incF : ∀ i, Function.Injective (inc i).onF
  conn : ∀ i, IsConnected (c i)
  zero : ∀ i < n, ZeroPi2 (inc i)
  pi1 : ∀ i, 1 ≤ i → i ≤ n → Pi1Trivial (inclFrom c inc i)
  proper : ∀ i < n, (¬ Function.Surjective (inc i).onE) ∨
    (¬ Function.Surjective (inc i).onF)

namespace RelativeCellChain
variable {c : ℕ → Complex2.{u}} {n : ℕ} (R : RelativeCellChain c n)

theorem inclV (i : ℕ) : Function.Injective (inclFrom c R.inc i).onV := by
  induction i with
  | zero => exact Function.injective_id
  | succ i hi => exact (R.incV i).comp hi
theorem inclE (i : ℕ) : Function.Injective (inclFrom c R.inc i).onE := by
  induction i with
  | zero => exact Function.injective_id
  | succ i hi => exact (R.incE i).comp hi
theorem inclF (i : ℕ) : Function.Injective (inclFrom c R.inc i).onF := by
  induction i with
  | zero => exact Function.injective_id
  | succ i hi => exact (R.incF i).comp hi

variable {K : Complex2.{u}} (p : Hom (c 0) K)

def desc : ℕ → Complex2.{u}
  | 0 => K
  | i + 1 => pushoutComplex p (inclFrom c R.inc (i + 1)) (R.inclV (i + 1)) (R.inclE (i + 1))

def descInc : ∀ i, Hom (R.desc p i) (R.desc p (i + 1))
  | 0 => pushoutInl p (inclFrom c R.inc 1) (R.inclV 1) (R.inclE 1)
  | i + 1 => pushoutFunctor p (inclFrom c R.inc (i + 1)) (inclFrom c R.inc (i + 2))
      (R.inc (i + 1)) (R.inclV (i + 1)) (R.inclE (i + 1))
      (R.inclV (i + 2)) (R.inclE (i + 2)) (R.inclF (i + 2)) rfl

theorem descInc_injective_V : ∀ i, Function.Injective (R.descInc p i).onV
  | 0 => Sum.inl_injective
  | i + 1 => RelChainW.pushoutFunctor_injV K p _ _ _ _ _ _ _ _ rfl (R.incV (i + 1))
theorem descInc_injective_E : ∀ i, Function.Injective (R.descInc p i).onE
  | 0 => Sum.inl_injective
  | i + 1 => RelChainW.pushoutFunctor_injE K p _ _ _ _ _ _ _ _ rfl (R.incE (i + 1))
theorem descInc_injective_F : ∀ i, Function.Injective (R.descInc p i).onF
  | 0 => Sum.inl_injective
  | i + 1 => RelChainW.pushoutFunctor_injF K p _ _ _ _ _ _ _ _ rfl (R.incF (i + 1))

theorem desc_connected (hp : IsCovering p) (d₀ : (c 0).V) : ∀ i, IsConnected (R.desc p i)
  | 0 => isConnected_of_covering p hp (R.conn 0)
  | i + 1 => isConnected_pushoutComplex p (inclFrom c R.inc (i + 1))
      (R.inclV (i + 1)) (R.inclE (i + 1))
      (isConnected_of_covering p hp (R.conn 0)) (R.conn (i + 1)) d₀

theorem descInc_proper (i : ℕ) (hi : i < n) :
    (¬ Function.Surjective (R.descInc p i).onE) ∨
      (¬ Function.Surjective (R.descInc p i).onF) := by
  rcases R.proper i hi with hE | hF
  · left
    cases i with
    | zero =>
        have hnonsurj : ∃ e, ∀ d, (R.inc 0).onE d ≠ e := by
          simpa only [Function.Surjective, not_forall, not_exists] using hE
        obtain ⟨e, he⟩ := hnonsurj
        have hn : ∀ d, (inclFrom c R.inc 1).onE d ≠ e := by
          intro d hd
          exact he d (by simpa only [inclFrom, Hom.comp, Hom.id, Function.comp_def, id_eq] using hd)
        intro hs
        obtain ⟨x, hx⟩ := hs (Sum.inr (⟨e, hn⟩ : OffE (inclFrom c R.inc 1)))
        exact Sum.inl_ne_inr hx
    | succ i => exact pushoutFunctor_not_surjective_E p _ _ _ _ _ _ _ _ rfl hE
  · right
    cases i with
    | zero =>
        have hnonsurj : ∃ e, ∀ d, (R.inc 0).onF d ≠ e := by
          simpa only [Function.Surjective, not_forall, not_exists] using hF
        obtain ⟨e, he⟩ := hnonsurj
        have hn : ∀ d, (inclFrom c R.inc 1).onF d ≠ e := by
          intro d hd
          exact he d (by simpa only [inclFrom, Hom.comp, Hom.id, Function.comp_def, id_eq] using hd)
        intro hs
        obtain ⟨x, hx⟩ := hs (Sum.inr (⟨e, hn⟩ : OffF (inclFrom c R.inc 1)))
        exact Sum.inl_ne_inr hx
    | succ i => exact pushoutFunctor_not_surjective_F p _ _ _ _ _ _ _ _ rfl hF

theorem descInc_zeroPi2 (hp : IsCovering p) {Q : Type v} [Group Q]
    (a : DeckAction (c 0) Q) (hr : IsRegular p a)
    (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
    (hf : ∀ q f, p.onF (a.smulF q f) = p.onF f)
    (hD : IsAcyclic (c 0)) (d₀ : (c 0).V) : ∀ i < n, ZeroPi2 (R.descInc p i)
  | 0, hi => zeroPi2_pushoutInl (inclFrom c R.inc 1) (R.inclV 1) (R.inclE 1) (R.inclF 1)
      hp hD (R.conn 0) (isConnected_of_covering p hp (R.conn 0)) (R.conn 1)
      (R.pi1 1 le_rfl (by omega))
  | i + 1, hi => by
      apply zeroPi2_pushoutFunctor p _ _ _ _ _ _ _ _ _ rfl
        (R.desc_connected p hp d₀ (i + 2)) (R.zero (i + 1) hi)
      intro x z hz
      exact regularCover_cycle_mem_pi2FromSub_span p hp a hr he hf (R.conn 0) hD d₀
        (inclFrom c R.inc (i + 1)) (R.inclV (i + 1)) (R.inclE (i + 1))
        (R.inclF (i + 1)) (R.conn (i + 1))
        (R.pi1 (i + 1) (by omega) (by omega)) x z hz

end RelativeCellChain
end FiniteChains.Comb
