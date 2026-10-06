import RequestProject.ChamberQuotientChosenInclusion
import RequestProject.UniversalCoverBaseTransport

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

def qBaseCanonicalRoot (x : X) : QLiftedBase (qNew (A := A) (att := att) x) :=
  ⟨UV.base (orderCx (Qpos A X att)) (qNew (A := A) (att := att) x), ⟨x, rfl⟩⟩

theorem qBaseCanonicalRoot_projection (x : X) :
    qBaseCoverEnd (X := X) (qNew (A := A) (att := att) x) (qBaseCanonicalRoot x) = x := by
  exact Sum.inr.inj (qBaseCoverEnd_spec (X := X) (qNew (A := A) (att := att) x) (qBaseCanonicalRoot x))

noncomputable def qBaseCanonicalLift (x : X) :
    Hom (uCover (orderCx X)
      (qBaseCoverEnd (X := X) (qNew (A := A) (att := att) x) (qBaseCanonicalRoot x)))
      (uCover (orderCx (Qpos A X att)) (qNew (A := A) (att := att) x)) :=
  (univLift (orderCx X) (orderCxMap (qNew (X := X) (A := A) (att := att)) qNew_monotone) x).comp
    (uCoverBaseTransport (K := orderCx X) (qBaseCanonicalRoot_projection (A := A) (att := att) x))

/-- The chosen-component inclusion at the canonical root is the canonical
universal-cover lift of the inserted original base. -/
theorem qBaseChosenInclusion_eq_canonical_onF (x : X)
    (hc : IsConnected (orderCx (Qpos A X att))) (hx : IsConnected (orderCx X)) :
    ∀ t, (qBaseChosenInclusion (qBaseCanonicalRoot (A := A) (att := att) x) hc hx).onF t =
      (qBaseCanonicalLift x).onF t := by
  apply qBaseChosenInclusion_onF_unique (qBaseCanonicalRoot (A := A) (att := att) x)
    hc hx (qBaseCanonicalLift (A := A) (att := att) x)
  · change (univLift (orderCx X) (orderCxMap (qNew (X := X) (A := A) (att := att)) qNew_monotone) x).onV ((uCoverBaseTransport (K := orderCx X) (qBaseCanonicalRoot_projection (A := A) (att := att) x)).onV
      (UV.base _ _)) = _
    rw (config := { transparency := .default }) [uCoverBaseTransport_base]
    rfl
  · intro e
    change (orderCxMap (qNew (X := X) (A := A) (att := att)) qNew_monotone).onE
      (((uCoverBaseTransport (K := orderCx X) (qBaseCanonicalRoot_projection (A := A) (att := att) x)).onE e).1.2) = _
    rw (config := { transparency := .default }) [uCoverBaseTransport_edge]
  · intro t
    change (orderCxMap (qNew (X := X) (A := A) (att := att)) qNew_monotone).onF
      (((uCoverBaseTransport (K := orderCx X) (qBaseCanonicalRoot_projection (A := A) (att := att) x)).onF t).1.2) = _
    rw (config := { transparency := .default }) [uCoverBaseTransport_face]

/-- Generation uses standard deck translates of the canonical inserted-base lift. -/
theorem qBaseDeckCoverFaceMap_eq_canonical (x : X)
    (hc : IsConnected (orderCx (Qpos A X att))) (hx : IsConnected (orderCx X))
    (g : Pi1 (orderCx (Qpos A X att)) (qNew (A := A) (att := att) x))
    (t : UF (orderCx X)
      (qBaseCoverEnd (X := X) (qNew (A := A) (att := att) x) (qBaseCanonicalRoot x))) :
    qBaseDeckCoverFaceMap (qBaseCanonicalRoot x) g hc hx t =
      deckF g ((qBaseCanonicalLift x).onF t) := by
  rw (config := { transparency := .default }) [qBaseDeckCoverFaceMap_eq_deckF, qBaseDeckCoverFaceMap_one,
    qBaseChosenInclusion_eq_canonical_onF]

end FiniteChains.Davis
