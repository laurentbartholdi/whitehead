import RequestProject.ZeroPi2Descent
import RequestProject.OrderUniversalRealizationSimplyConnected
import RequestProject.OrderNerveRealizationNestedSubcomplex
import RequestProject.TopologicalCockcroft

namespace FiniteChains.Comb
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

/-- The path-class lift of a pi1-trivial order map preserves the lifted order. -/
theorem order_liftV_monotone (f : P → Q) (hf : Monotone f)
    (hc : IsConnected (orderCx P)) (a : P) (ht : Pi1Trivial (orderCxMap f hf)) :
    Monotone (α := P) (β := UOrder Q (f a)) (liftV (orderCxMap f hf) hc a) := by
  intro x y hxy
  have he (v : P) : uOrderEnd (liftV (orderCxMap f hf) hc a v) = f v :=
    endV_liftV hc v
  refine ⟨(he x).le.trans ((hf hxy).trans (he y).ge), ?_⟩
  have h := liftV_extend hc (d₀ := a) ht (ordPos hxy)
  change liftV (orderCxMap f hf) hc a y =
    extend ((orderCxMap f hf).onE (ordPos hxy).1, true)
      (liftV (orderCxMap f hf) hc a x) at h
  change extend (ordPos _) (liftV (orderCxMap f hf) hc a x) = _
  calc
    _ = extend ((orderCxMap f hf).onE (ordPos hxy).1, true)
        (liftV (orderCxMap f hf) hc a x) := by
      congr 1
      apply Prod.ext
      · apply Subtype.ext
        exact Prod.ext (he x) (he y)
      · rfl
    _ = _ := h.symm

/-- A monotone lift into the constructed simply connected universal order. -/
noncomputable def orderPi1TrivialLift (f : P → Q) (hf : Monotone f)
    (hc : IsConnected (orderCx P)) (a : P) (ht : Pi1Trivial (orderCxMap f hf)) :
    P →o UOrder Q (f a) :=
  ⟨liftV (orderCxMap f hf) hc a, order_liftV_monotone f hf hc a ht⟩

theorem orderPi1TrivialLift_end (f : P → Q) (hf : Monotone f)
    (hc : IsConnected (orderCx P)) (a : P) (ht : Pi1Trivial (orderCxMap f hf)) (v : P) :
    uOrderEnd (orderPi1TrivialLift f hf hc a ht v) = f v := endV_liftV hc v

/-- The genuine realization factors through a simply connected space whenever
the order-complex map kills combinatorial pi1. -/
theorem orderPi1TrivialLift_realization (f : P → Q) (hf : Monotone f)
    (hc : IsConnected (orderCx P)) (a : P) (ht : Pi1Trivial (orderCxMap f hf))
    (x : orderNerveRealization P) :
    orderNerveRealizationMap uOrderEnd uOrderEnd_monotone
      (orderNerveRealizationMap (orderPi1TrivialLift f hf hc a ht)
        (orderPi1TrivialLift f hf hc a ht).monotone x) =
      orderNerveRealizationMap f hf x := by
  rw [orderNerveRealizationMap_comp]
  have he : uOrderEnd ∘ orderPi1TrivialLift f hf hc a ht = f :=
    funext (orderPi1TrivialLift_end f hf hc a ht)
  have hm : (⟨uOrderEnd ∘ orderPi1TrivialLift f hf hc a ht,
      uOrderEnd_monotone.comp (orderPi1TrivialLift f hf hc a ht).monotone⟩ :
      {g : P → Q // Monotone g}) = ⟨f, hf⟩ := Subtype.ext he
  exact congrArg (fun g => orderNerveRealizationMap g.1 g.2 x) hm

/-- A proved combinatorial pi1 calculation now gives actual triviality on pi2
for a Cockcroft realization. No pi2 generation assumption is used. -/
theorem killsPi2_orderRealization_of_isCockcroft_of_pi1Trivial
    (f : P → Q) (hf : Monotone f) (hc : IsConnected (orderCx P)) (a : P)
    (ht : Pi1Trivial (orderCxMap f hf))
    (hP : Whitehead.IsCockcroft (orderNerveRealization P)) :
    Whitehead.KillsPi2
      ⟨orderNerveRealizationMap f hf, (orderNerveRealizationMap f hf).hom.continuous⟩ := by
  letI := uOrderRealization_simplyConnected (f a)
  let l := orderPi1TrivialLift f hf hc a ht
  let g : C(orderNerveRealization P, orderNerveRealization (UOrder Q (f a))) :=
    ⟨orderNerveRealizationMap l l.monotone, (orderNerveRealizationMap l l.monotone).hom.continuous⟩
  let p : C(orderNerveRealization (UOrder Q (f a)), orderNerveRealization Q) :=
    ⟨orderNerveRealizationMap uOrderEnd uOrderEnd_monotone,
      (orderNerveRealizationMap uOrderEnd uOrderEnd_monotone).hom.continuous⟩
  have he : p.comp g =
      ⟨orderNerveRealizationMap f hf, (orderNerveRealizationMap f hf).hom.continuous⟩ := by
    apply ContinuousMap.ext
    exact orderPi1TrivialLift_realization f hf hc a ht
  rw [← he]
  exact Whitehead.killsPi2_of_isCockcroft_factorization hP g p

end FiniteChains.Comb
