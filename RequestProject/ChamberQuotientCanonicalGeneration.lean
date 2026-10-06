import RequestProject.ChamberQuotientCanonicalInclusion

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] [Nonempty X] {att : NeSpx A →o X}

/-- Actual quotient cycles are generated modulo lifted three-boundaries by the
standard deck translates of cycles under the canonical original-base inclusion. -/
theorem exists_qCover_canonical_base_cycles
    (w : {w : CayGroup A // IsGamma A w}) (x : X)
    (hc : IsConnected (orderCx (Zpos A X (IsGamma A) att)))
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
  classical
  obtain ⟨s, g, d, hd, y, he⟩ := exists_qCover_equivariant_base_cycles
    (zNew w x) hc hx (qBaseCanonicalRoot x) z hz
  let T := uCoverBaseTransport (K := orderCx X)
    (qBaseCanonicalRoot_projection (A := A) (att := att) x)
  refine ⟨s, g, fun i => chain2 T (d i), ?_, y, ?_⟩
  · intro i
    have hi : Comb.bdry2
        (uCover (orderCx X) (qBaseCoverEnd (X := X) (qNew (A := A) (att := att) x)
          (qBaseCanonicalRoot x))) (d i) = 0 := hd i
    rw (config := { transparency := .default }) [bdry2_chain2, hi, map_zero]
  · rw (config := { transparency := .default }) [he]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    change Finsupp.mapDomain _ (d i) = Finsupp.mapDomain _ (Finsupp.mapDomain T.onF (d i))
    rw (config := { transparency := .default }) [← Finsupp.mapDomain_comp]
    apply Finsupp.mapDomain_congr
    intro t _
    exact qBaseDeckCoverFaceMap_eq_canonical x (qpos_isConnected_of_zpos hc) hx (g i) t

end FiniteChains.Davis
