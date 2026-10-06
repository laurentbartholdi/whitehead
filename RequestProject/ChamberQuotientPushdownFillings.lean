import RequestProject.OrderNerveH2Maps
import RequestProject.ChamberQuotientConnectedGeneration
import RequestProject.OrderUniversalBoundaryProjection

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

/-- Actual zero homology pushdown of base cover cycles is preserved by the
constructed quotient chamber extension. -/
theorem qCover_pushdown_filling_of_base (x : X)
    (hx : IsConnected (orderCx X))
    (hbase : ∀ c : UF (orderCx X) x →₀ ℤ,
      Comb.bdry2 (uCover (orderCx X) x) c = 0 →
        ∃ y : OrdTet X →₀ ℤ,
          chain2 (univProj (X := orderCx X) (x₀ := x)) c = ordBoundary3 y)
    (z : UF (orderCx (Qpos A X att)) (qNew (A := A) (att := att) x) →₀ ℤ)
    (hz : Comb.bdry2 (uCover (orderCx (Qpos A X att)) (qNew (A := A) (att := att) x)) z = 0) :
    ∃ y : OrdTet (Qpos A X att) →₀ ℤ,
      chain2 (univProj (X := orderCx (Qpos A X att)) (x₀ := qNew (A := A) (att := att) x)) z = ordBoundary3 y := by
  classical
  obtain ⟨s, g, d, hd, y, he⟩ := exists_qCover_canonical_base_cycles_of_connected x hx z hz
  choose b hb using fun i => hbase (d i) (hd i)
  obtain ⟨v, hv⟩ := univProj_uOrdBoundary3 y
  refine ⟨(∑ i ∈ s, Finsupp.mapDomain (ordTetMap (qNew (A := A) (att := att)) qNew_monotone) (b i)) + v, ?_⟩
  rw (config := { transparency := .default }) [he, map_add, map_sum, hv, map_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hp := univProj_deck_lift_chain2 (X := orderCx X)
    (Y := orderCx (Qpos A X att)) x
    (orderCxMap (qNew (A := A) (att := att)) qNew_monotone) (g i) (d i)
  apply hp.trans
  rw (config := { transparency := .default }) [hb i]
  exact chain2_ordBoundary3 (qNew (A := A) (att := att)) qNew_monotone (b i)

/-- Zero pushdown on actual second homology is preserved by the constructed
quotient chamber extension. -/
theorem qCover_homology_pushdown_map_zero_of_base (x : X)
    (hx : IsConnected (orderCx X))
    (hbase : ∀ c : UF (orderCx X) x →₀ ℤ,
      Comb.bdry2 (uCover (orderCx X) x) c = 0 →
        ∃ y : OrdTet X →₀ ℤ,
          chain2 (univProj (X := orderCx X) (x₀ := x)) c = ordBoundary3 y) :
    orderNerveH2Map
      (uOrderEnd : UOrder (Qpos A X att) (qNew (A := A) (att := att) x) → Qpos A X att)
      uOrderEnd_monotone = 0 := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H c =>
    change orderNerveH2Map uOrderEnd uOrderEnd_monotone
      (orderNerveH2Class _ c.val c.property) = 0
    rw (config := { transparency := .default }) [orderNerveH2Map_class]
    apply (orderNerveH2Class_eq_zero_iff _ _ _).mpr
    have hc : Comb.bdry2 (uCover (orderCx (Qpos A X att))
        (qNew (A := A) (att := att) x)) (uOrderChain2Equiv c.val) = 0 :=
      (uOrderHom_cycle_iff c.val).mpr c.property
    obtain ⟨y, hy⟩ := qCover_pushdown_filling_of_base x hx hbase _ hc
    rw (config := { transparency := .default }) [uOrderChain2Equiv_projection] at hy
    exact ⟨y, hy.symm⟩

/-- The actual zero universal-cover pushdown map on second homology is preserved
by the constructed quotient chamber extension. -/
theorem qCover_homology_pushdown_map_zero (x : X)
    (hx : IsConnected (orderCx X))
    (hzero : orderNerveH2Map (uOrderEnd : UOrder X x → X) uOrderEnd_monotone = 0) :
    orderNerveH2Map
      (uOrderEnd : UOrder (Qpos A X att) (qNew (A := A) (att := att) x) → Qpos A X att)
      uOrderEnd_monotone = 0 :=
  qCover_homology_pushdown_map_zero_of_base x hx
    (univCover_pushdown_filling_of_homology_zero hzero)

end FiniteChains.Davis
