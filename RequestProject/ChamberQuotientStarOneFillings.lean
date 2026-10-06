module

public import RequestProject.ChamberQuotientLiftedStarRetraction
public import RequestProject.ChamberQuotientBaseSimplyConnected
public import RequestProject.ChamberZConnected
public import RequestProject.OrderSimplyConnectedOneFillings
public import RequestProject.NerveLowerMapFillings

@[expose] public section

/-! Every one-cycle of the actual lifted base star has a finite filling there. -/
namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

theorem qLiftedBaseStar_oneCycle_filling (a : Qpos A X att)
    (hc : IsConnected (orderCx (Qpos A X att)))
    (c : Ch (QLiftedBaseStar a)) (hi : c ∈ Inc _)
    (hd : lengthProjection 2 c = c) (hcyc : Nerve.bdry c = 0) :
    ∃ y ∈ Inc (QLiftedBaseStar a), Nerve.bdry y = c :=
  filling_of_lower_composite (qLiftedStarRetraction a hc) (qBaseIntoStar a)
    (qLiftedStarRetraction_monotone a hc) (qBaseIntoStar_monotone a)
    (qLiftedStarRetraction_le a hc) 2
    (nerve_oneCycle_filling_of_simplyConnected (qLiftedBase_simplyConnected a hc))
    c hi hd hcyc

theorem qUniversal_baseStar_fillsDegree_two (x : X) (hx : IsConnected (orderCx X)) :
    FillsDegreeIn
      (fun p : UOrder (Qpos A X att) (qNew x) => InQBaseStar (uOrderEnd p)) 2 := by
  letI : Nonempty X := ⟨x⟩
  have hc : IsConnected (orderCx (Qpos A X att)) :=
    qpos_isConnected_of_zpos (zpos_isConnected hx)
  apply fillsDegreeIn_of_subtype
  · obtain ⟨p, hp⟩ := (uOrderEnd_isPosetCover (a := qNew x) hc).surj (qNew x)
    exact ⟨p, by rw [hp]; trivial⟩
  · exact qLiftedBaseStar_oneCycle_filling (qNew x) hc

end FiniteChains.Davis
