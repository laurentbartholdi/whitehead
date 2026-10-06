module

public import RequestProject.ChamberQuotientConnectedGeneration
public import RequestProject.PresPosetConnected
public import RequestProject.PresPosetPartialOrder

@[expose] public section

namespace FiniteChains.Davis
open RACG Mirror Comb PresModel
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {α J : Type u}

/-- Canonical quotient-cover cycle generation for the actual connected presentation model. -/
theorem presPos_quotient_cycle_generation
    (w : J → List (α × Bool)) (hw : ∀ j, w j ≠ [])
    (att : NeSpx A →o PresPos w)
    (z : UF (orderCx (Qpos A (PresPos w) att)) (qNew (ptBase w)) →₀ ℤ)
    (hz : Comb.bdry2 (uCover (orderCx (Qpos A (PresPos w) att)) (qNew (ptBase w))) z = 0) :
    ∃ (s : Finset (OrderComponent (QLiftedBase (qNew (A := A) (att := att) (ptBase w)))))
      (g : OrderComponent (QLiftedBase (qNew (A := A) (att := att) (ptBase w))) →
        Pi1 (orderCx (Qpos A (PresPos w) att)) (qNew (ptBase w)))
      (d : OrderComponent (QLiftedBase (qNew (A := A) (att := att) (ptBase w))) →
        (UF (orderCx (PresPos w)) (ptBase w) →₀ ℤ)),
      (∀ i, Comb.bdry2 (uCover (orderCx (PresPos w)) (ptBase w)) (d i) = 0) ∧
      ∃ y : UOrdTet (Qpos A (PresPos w) att) (qNew (ptBase w)) →₀ ℤ,
        z = (∑ i ∈ s, Finsupp.mapDomain
          (deckF (g i) ∘ univLiftF (ptBase w)
            (orderCxMap (qNew (X := PresPos w) (A := A) (att := att)) qNew_monotone)) (d i)) +
          uOrdBoundary3 y := by
  exact exists_qCover_canonical_base_cycles_of_connected (ptBase w)
    (presPos_isConnected w hw) z hz

end FiniteChains.Davis
