module

public import RequestProject.OrderPathCoverPi2Criterion
public import RequestProject.ChamberQuotientImageFillings
public import RequestProject.ChamberTopologicalCockcroft
public import RequestProject.OrderPi1TrivialLift

@[expose] public section

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [Fintype V] {A : CommRel V}
variable {X R : Type} [PartialOrder X] [PartialOrder R] {att : NeSpx A →o X}

/-- A map from the chamber quotient kills actual pi2 whenever its restriction
to the original base does. No pi2-generation or Hurewicz comparison premise remains. -/
theorem killsPi2_qpos_of_base (x : X) (hX : IsConnected (orderCx X))
    (hR : IsConnected (orderCx R)) (f : Qpos A X att → R) (hf : Monotone f)
    (hb : Whitehead.KillsPi2
      ⟨orderNerveRealizationMap (f ∘ qNew (A := A) (att := att)) (hf.comp qNew_monotone),
        (orderNerveRealizationMap (f ∘ qNew (A := A) (att := att))
          (hf.comp qNew_monotone)).hom.continuous⟩) :
    Whitehead.KillsPi2
      ⟨orderNerveRealizationMap f hf, (orderNerveRealizationMap f hf).hom.continuous⟩ := by
  letI : Nonempty X := ⟨x⟩
  apply (killsPi2_orderRealization_iff_pathCover_cycles_bound f hf (qNew x)
    (qpos_isConnected hX) hR).mpr
  exact qCover_image_filling_of_base x hX f hf
    ((killsPi2_orderRealization_iff_pathCover_cycles_bound
      (f ∘ qNew (A := A) (att := att)) (hf.comp qNew_monotone) x hX hR).mp hb)

/-- In the terminal-step situation, combinatorial triviality of the restriction
on pi1 suffices to kill actual pi2 on the entire chamber quotient. -/
theorem killsPi2_qpos_of_isCockcroft_of_base_pi1Trivial
    (x : X) (hX : IsConnected (orderCx X)) (hR : IsConnected (orderCx R))
    (hc : Whitehead.IsCockcroft (orderNerveRealization X))
    (f : Qpos A X att → R) (hf : Monotone f)
    (ht : Pi1Trivial (orderCxMap (f ∘ qNew (A := A) (att := att))
      (hf.comp qNew_monotone))) :
    Whitehead.KillsPi2
      ⟨orderNerveRealizationMap f hf, (orderNerveRealizationMap f hf).hom.continuous⟩ :=
  killsPi2_qpos_of_base x hX hR f hf
    (killsPi2_orderRealization_of_isCockcroft_of_pi1Trivial
      (f ∘ qNew (A := A) (att := att)) (hf.comp qNew_monotone) hX x ht hc)

end FiniteChains.Davis
