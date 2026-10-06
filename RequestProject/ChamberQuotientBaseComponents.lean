module

public import RequestProject.ChamberQuotientBaseSimplyConnected
public import RequestProject.OrderComponentCover
public import RequestProject.SimplyConnectedCoverEquiv

@[expose] public section

/-! Genuine universal-cover cells and cycles in each actual lifted base component. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

abbrev QBaseComponent (a : Qpos A X att) (b : QLiftedBase a) :=
  OrderReachComponent (QLiftedBase a) b

variable (a : Qpos A X att) (hc : IsConnected (orderCx (Qpos A X att)))
  (hx : IsConnected (orderCx X)) (b : QLiftedBase a)

noncomputable def qBaseComponentProjection : Hom (orderCx (QBaseComponent a b)) (orderCx X) :=
  orderCxMap (orderComponentProjection (qBaseCoverEnd a) b)
    ((qBaseCoverEnd_isPosetCover a hc).reachableRestriction hx b).mono

omit [Fintype V] in
theorem qBaseComponentProjection_isCovering : IsCovering (qBaseComponentProjection a hc hx b) :=
  isCovering_orderCxMap ((qBaseCoverEnd_isPosetCover a hc).reachableRestriction hx b)

include hc hx in
omit [Fintype V] in
theorem qBaseComponent_isConnected : IsConnected (orderCx (QBaseComponent a b)) :=
  orderReachComponent_isConnected (qBaseCoverEnd_isPosetCover a hc) hx b

include hc hx in
theorem qBaseComponent_simplyConnected : SimplyConnected (orderCx (QBaseComponent a b)) :=
  orderReachComponent_simplyConnected (qBaseCoverEnd_isPosetCover a hc) hx
    (qLiftedBase_simplyConnected a hc) b

def qBaseComponentRoot : (orderCx (QBaseComponent a b)).V :=
  ⟨b, reach_self (orderCx (QLiftedBase a)) b⟩

noncomputable def qBaseComponentUniversalHom :
    Hom (uCover (orderCx X) (qBaseCoverEnd (X := X) a b)) (orderCx (QBaseComponent a b)) :=
  coverHom (qBaseComponentProjection_isCovering a hc hx b)
    (d₀ := qBaseComponentRoot a b) rfl

theorem qBaseComponentUniversalHom_onF_bijective :
    Function.Bijective (qBaseComponentUniversalHom a hc hx b).onF := by
  change Function.Bijective (coverF (qBaseComponentProjection_isCovering a hc hx b)
    (d₀ := qBaseComponentRoot a b) rfl)
  exact ⟨coverF_injective (qBaseComponentProjection_isCovering a hc hx b)
      (qBaseComponent_simplyConnected a hc hx b),
    coverF_surjective (qBaseComponentProjection_isCovering a hc hx b)
      (qBaseComponent_isConnected a hc hx b)⟩

theorem qBaseComponentUniversalHom_onE_injective :
    Function.Injective (qBaseComponentUniversalHom a hc hx b).onE := by
  change Function.Injective (coverE (qBaseComponentProjection_isCovering a hc hx b)
    (d₀ := qBaseComponentRoot a b) rfl)
  exact coverE_injective (qBaseComponentProjection_isCovering a hc hx b)
    (qBaseComponent_simplyConnected a hc hx b)

/-- Every finite two-cycle of the actual lifted component comes from a unique
genuine universal-cover two-cycle of the original base. -/
theorem exists_unique_qBaseComponent_cycle
    (c : OrdTri (QBaseComponent a b) →₀ ℤ)
    (hc' : Comb.bdry2 (orderCx (QBaseComponent a b)) c = 0) :
    ∃! d : UF (orderCx X) (qBaseCoverEnd (X := X) a b) →₀ ℤ,
      chain2 (qBaseComponentUniversalHom a hc hx b) d = c ∧
      Comb.bdry2 (uCover (orderCx X) (qBaseCoverEnd (X := X) a b)) d = 0 := by
  obtain ⟨d, hd⟩ := Finsupp.mapDomain_surjective
    (qBaseComponentUniversalHom_onF_bijective a hc hx b).2 c
  have hd' : chain2 (qBaseComponentUniversalHom a hc hx b) d = c := hd
  refine ⟨d, ⟨hd', ?_⟩, ?_⟩
  · apply Finsupp.mapDomain_injective (qBaseComponentUniversalHom_onE_injective a hc hx b)
    change chain1 (qBaseComponentUniversalHom a hc hx b)
      (Comb.bdry2 (uCover (orderCx X) (qBaseCoverEnd (X := X) a b)) d) =
        Finsupp.mapDomain _ 0
    rw [Finsupp.mapDomain_zero, ← bdry2_chain2, hd', hc']
  · intro e he
    exact Finsupp.mapDomain_injective (qBaseComponentUniversalHom_onF_bijective a hc hx b).1
      (he.1.trans hd'.symm)

end FiniteChains.Davis
