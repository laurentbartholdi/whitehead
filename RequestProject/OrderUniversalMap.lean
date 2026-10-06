import RequestProject.CombPi2
import RequestProject.OrderUniversalPosetHom
import RequestProject.OrderNerveRealizationNestedSubcomplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

theorem uOrderMap_monotone (f : P → Q) (hf : Monotone f) (a : P) :
    Monotone (α := UOrder P a) (β := UOrder Q (f a))
      (@univLiftV (orderCx P) (orderCx Q) a (orderCxMap f hf)) := by
  intro v w hvw
  have he (v : UOrder P a) :
      uOrderEnd (@univLiftV (orderCx P) (orderCx Q) a (orderCxMap f hf) v) = f (uOrderEnd v) :=
    @endV_univLiftV (orderCx P) (orderCx Q) a (orderCxMap f hf) v
  refine ⟨(he v).le.trans ((hf hvw.1).trans (he w).ge), ?_⟩
  have h := univLiftV_extend (X := orderCx P) (Y := orderCx Q) a (orderCxMap f hf) (eb := ordPos hvw.1) (c := v) rfl
  have hw : extend (ordPos hvw.1) v = w := hvw.2
  rw (config := { transparency := .default }) [hw] at h
  change extend (ordPos _) (@univLiftV (orderCx P) (orderCx Q) a (orderCxMap f hf) v) = _
  calc
    _ = extend ((orderCxMap f hf).onE (ordPos hvw.1).1, true)
        (@univLiftV (orderCx P) (orderCx Q) a (orderCxMap f hf) v) := by
      congr 1
      apply Prod.ext
      · apply Subtype.ext
        exact Prod.ext (he v) (he w)
      · rfl
    _ = _ := h.symm

/-- Functorial map between the actual ordered universal covers. -/
noncomputable def uOrderMap (f : P → Q) (hf : Monotone f) (a : P) :
    UOrder P a →o UOrder Q (f a) :=
  ⟨@univLiftV (orderCx P) (orderCx Q) a (orderCxMap f hf), uOrderMap_monotone f hf a⟩

theorem uOrderMap_end (f : P → Q) (hf : Monotone f) (a : P) (v : UOrder P a) :
    uOrderEnd (uOrderMap f hf a v) = f (uOrderEnd v) :=
  @endV_univLiftV (orderCx P) (orderCx Q) a (orderCxMap f hf) v

theorem uOrderMap_face (f : P → Q) (hf : Monotone f) (a : P)
    (t : OrdTri (UOrder P a)) :
    uOrderFace ((orderCxMap (uOrderMap f hf a) (uOrderMap f hf a).monotone).onF t) =
      (univLift (orderCx P) (orderCxMap f hf) a).onF (uOrderFace t) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact Prod.ext (uOrderMap_end f hf a t.1.1)
      (Prod.ext (uOrderMap_end f hf a t.1.2.1) (uOrderMap_end f hf a t.1.2.2))

theorem uOrderMap_chain2 (f : P → Q) (hf : Monotone f) (a : P)
    (c : OrdTri (UOrder P a) →₀ ℤ) :
    chain2 uOrderHom (chain2
      (orderCxMap (uOrderMap f hf a) (uOrderMap f hf a).monotone) c) =
    chain2 (univLift (orderCx P) (orderCxMap f hf) a) (chain2 uOrderHom c) := by
  change Finsupp.mapDomain uOrderFace (Finsupp.mapDomain _ c) =
    Finsupp.mapDomain _ (Finsupp.mapDomain uOrderFace c)
  rw (config := { transparency := .default }) [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  exact congrArg (fun g => Finsupp.mapDomain g c) (funext (uOrderMap_face f hf a))

theorem uOrderMap_realization_projection (f : P → Q) (hf : Monotone f) (a : P)
    (x : orderNerveRealization (UOrder P a)) :
    orderNerveRealizationMap uOrderEnd uOrderEnd_monotone
      (orderNerveRealizationMap (uOrderMap f hf a) (uOrderMap f hf a).monotone x) =
    orderNerveRealizationMap f hf
      (orderNerveRealizationMap uOrderEnd uOrderEnd_monotone x) := by
  rw (config := { transparency := .default }) [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
  have hm : (⟨uOrderEnd ∘ uOrderMap f hf a,
      uOrderEnd_monotone.comp (uOrderMap f hf a).monotone⟩ :
      {g : UOrder P a → Q // Monotone g}) =
      ⟨f ∘ uOrderEnd, hf.comp uOrderEnd_monotone⟩ :=
    Subtype.ext (funext (uOrderMap_end f hf a))
  exact congrArg (fun g => orderNerveRealizationMap g.1 g.2 x) hm

end FiniteChains.Comb
