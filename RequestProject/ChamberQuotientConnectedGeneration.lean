import RequestProject.ChamberQuotientCanonicalGeneration
import RequestProject.ChamberZConnected

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

/-- Canonical finite equivariant generation needs only connectivity of the original base. -/
theorem exists_qCover_canonical_base_cycles_of_connected
    (x : X)
    (hx : IsConnected (orderCx X))
    (z : UF (orderCx (Qpos A X att)) (qNew x) →₀ ℤ)
    (hz : Comb.bdry2 (uCover (orderCx (Qpos A X att)) (qNew x)) z = 0) :
    ∃ (s : Finset (OrderComponent (QLiftedBase (qNew (A := A) (att := att) x))))
      (g : OrderComponent (QLiftedBase (qNew (A := A) (att := att) x)) →
        Pi1 (orderCx (Qpos A X att)) (qNew x))
      (d : OrderComponent (QLiftedBase (qNew (A := A) (att := att) x)) →
        (UF (orderCx X) x →₀ ℤ)),
      (∀ i, Comb.bdry2 (uCover (orderCx X) x) (d i) = 0) ∧
      ∃ y : UOrdTet (Qpos A X att) (qNew x) →₀ ℤ,
        z = (∑ i ∈ s, Finsupp.mapDomain
          (deckF (g i) ∘ univLiftF x
            (orderCxMap (qNew (X := X) (A := A) (att := att)) qNew_monotone)) (d i)) +
          uOrdBoundary3 y := by
  letI : Nonempty X := ⟨x⟩
  exact exists_qCover_canonical_base_cycles ⟨1, isGamma_one⟩ x (zpos_isConnected hx) hx z hz

end FiniteChains.Davis
