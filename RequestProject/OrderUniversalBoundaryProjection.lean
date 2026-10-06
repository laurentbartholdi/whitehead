module

public import RequestProject.OrderNerveH2Maps
public import RequestProject.OrderUniversalChainProjection
public import RequestProject.OrderUniversalTetLift
public import RequestProject.OrderNerveCellMaps
public import RequestProject.CombPi2

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

/-- Projecting a genuine path-cover three-boundary gives a genuine finite
three-boundary in the base order nerve. -/
theorem univProj_uOrdBoundary3 (y : UOrdTet P a →₀ ℤ) :
    ∃ d : OrdTet P →₀ ℤ,
      chain2 (univProj (X := orderCx P) (x₀ := a)) (uOrdBoundary3 y) = ordBoundary3 d := by
  obtain ⟨c, rfl⟩ := exists_uOrder_three_chain y
  rw (config := { transparency := .default }) [← uOrderHom_ordBoundary3]
  change ∃ d : OrdTet P →₀ ℤ,
    chain2 (univProj (X := orderCx P) (x₀ := a))
      (uOrderChain2Equiv (ordBoundary3 c)) = ordBoundary3 d
  rw (config := { transparency := .default }) [uOrderChain2Equiv_projection]
  exact ⟨Finsupp.mapDomain (ordTetMap uOrderEnd uOrderEnd_monotone) c,
    chain2_ordBoundary3 uOrderEnd uOrderEnd_monotone c⟩

/-- Projection of a deck-translated lifted chain is the pushforward of its
original projection under the actual cellular map. -/
theorem univProj_deck_lift_chain2 {X Y : Complex2} (x : X.V) (h : Hom X Y)
    (g : Pi1 Y (h.onV x)) (c : UF X x →₀ ℤ) :
    chain2 (univProj (X := Y) (x₀ := h.onV x))
      (Finsupp.mapDomain (deckF g ∘ univLiftF x h) c) =
        chain2 h (chain2 (univProj (X := X) (x₀ := x)) c) := by
  change Finsupp.mapDomain (univProj (X := Y) (x₀ := h.onV x)).onF
    (Finsupp.mapDomain (deckF g ∘ univLiftF x h) c) =
      Finsupp.mapDomain h.onF
        (Finsupp.mapDomain (univProj (X := X) (x₀ := x)).onF c)
  simp only [← Finsupp.mapDomain_comp]
  rfl

/-- Vanishing of the actual universal-order homology pushdown supplies actual
finite fillings of every projected path-cover two-cycle. -/
theorem univCover_pushdown_filling_of_homology_zero
    (hzero : orderNerveH2Map (uOrderEnd : UOrder P a → P) uOrderEnd_monotone = 0)
    (c : UF (orderCx P) a →₀ ℤ)
    (hc : bdry2 (uCover (orderCx P) a) c = 0) :
    ∃ y : OrdTet P →₀ ℤ,
      chain2 (univProj (X := orderCx P) (x₀ := a)) c = ordBoundary3 y := by
  let r := uOrderChain2Equiv.symm c
  have hr : bdry2 (orderCx (UOrder P a)) r = 0 := by
    apply (uOrderHom_cycle_iff r).mp
    change bdry2 (uCover (orderCx P) a)
      (uOrderChain2Equiv (uOrderChain2Equiv.symm c)) = 0
    rw (config := { transparency := .default }) [uOrderChain2Equiv.apply_symm_apply]
    exact hc
  have hz := congrArg (fun m => m (orderNerveH2Class _ r hr)) hzero
  simp only [orderNerveH2Map_class, LinearMap.zero_apply] at hz
  obtain ⟨y, hy⟩ := (orderNerveH2Class_eq_zero_iff _ _ _).mp hz
  have hp := uOrderChain2Equiv_projection r
  rw (config := { transparency := .default }) [uOrderChain2Equiv.apply_symm_apply] at hp
  exact ⟨y, hp.trans hy.symm⟩

end FiniteChains.Comb
