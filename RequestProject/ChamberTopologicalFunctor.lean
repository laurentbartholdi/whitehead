import RequestProject.ChamberTopologicalPi2Descent
import RequestProject.ChamberQuotientFunctor
import RequestProject.SolutionLemmas

namespace FiniteChains.Comb
variable {P Q R : Type} [PartialOrder P] [PartialOrder Q] [PartialOrder R]

theorem killsPi2_orderRealization_comp (f : P → Q) (hf : Monotone f)
    (g : Q → R) (hg : Monotone g)
    (hk : Whitehead.KillsPi2
      ⟨orderNerveRealizationMap f hf, (orderNerveRealizationMap f hf).hom.continuous⟩) :
    Whitehead.KillsPi2
      ⟨orderNerveRealizationMap (g ∘ f) (hg.comp hf),
        (orderNerveRealizationMap (g ∘ f) (hg.comp hf)).hom.continuous⟩ := by
  let F : C(orderNerveRealization P, orderNerveRealization Q) :=
    ⟨orderNerveRealizationMap f hf, (orderNerveRealizationMap f hf).hom.continuous⟩
  let G : C(orderNerveRealization Q, orderNerveRealization R) :=
    ⟨orderNerveRealizationMap g hg, (orderNerveRealizationMap g hg).hom.continuous⟩
  have he : G.comp F =
      ⟨orderNerveRealizationMap (g ∘ f) (hg.comp hf),
        (orderNerveRealizationMap (g ∘ f) (hg.comp hf)).hom.continuous⟩ := by
    apply ContinuousMap.ext
    exact orderNerveRealizationMap_comp f hf g hg
  rw [← he]
  exact Whitehead.killsPi2_comp F G hk

theorem killsPi2_orderRealization_precomp (f : P → Q) (hf : Monotone f)
    (g : Q → R) (hg : Monotone g)
    (hk : Whitehead.KillsPi2
      ⟨orderNerveRealizationMap g hg, (orderNerveRealizationMap g hg).hom.continuous⟩) :
    Whitehead.KillsPi2
      ⟨orderNerveRealizationMap (g ∘ f) (hg.comp hf),
        (orderNerveRealizationMap (g ∘ f) (hg.comp hf)).hom.continuous⟩ := by
  let F : C(orderNerveRealization P, orderNerveRealization Q) :=
    ⟨orderNerveRealizationMap f hf, (orderNerveRealizationMap f hf).hom.continuous⟩
  let G : C(orderNerveRealization Q, orderNerveRealization R) :=
    ⟨orderNerveRealizationMap g hg, (orderNerveRealizationMap g hg).hom.continuous⟩
  have he : G.comp F =
      ⟨orderNerveRealizationMap (g ∘ f) (hg.comp hf),
        (orderNerveRealizationMap (g ∘ f) (hg.comp hf)).hom.continuous⟩ := by
    apply ContinuousMap.ext
    exact orderNerveRealizationMap_comp f hf g hg
  rw [← he]
  intro x p
  exact hk (F x) (Whitehead.mapSquare F p)

end FiniteChains.Comb

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [Fintype V] {A : CommRel V}
variable {X Y R : Type} [PartialOrder X] [PartialOrder Y] [PartialOrder R]

/-- The genuine pi2-killing condition on a chamber quotient is detected on its base. -/
theorem killsPi2_qpos_iff_base {att : NeSpx A →o X} (x : X)
    (hX : IsConnected (orderCx X)) (hR : IsConnected (orderCx R))
    (f : Qpos A X att → R) (hf : Monotone f) :
    Whitehead.KillsPi2
      ⟨orderNerveRealizationMap f hf, (orderNerveRealizationMap f hf).hom.continuous⟩ ↔
    Whitehead.KillsPi2
      ⟨orderNerveRealizationMap (f ∘ qNew (A := A) (att := att)) (hf.comp qNew_monotone),
        (orderNerveRealizationMap (f ∘ qNew (A := A) (att := att))
          (hf.comp qNew_monotone)).hom.continuous⟩ :=
  ⟨killsPi2_orderRealization_precomp (qNew (A := A) (att := att)) qNew_monotone f hf,
    killsPi2_qpos_of_base x hX hR f hf⟩

/-- Applying the chamber construction to an order map preserves vanishing on
actual pi2. This proves the structural-map implication for these constructed spaces. -/
theorem qposMap_preserves_killsPi2 (att : NeSpx A →o X) (f : X →o Y)
    (x : X) (hX : IsConnected (orderCx X)) (hY : IsConnected (orderCx Y))
    (hk : Whitehead.KillsPi2
      ⟨orderNerveRealizationMap f f.monotone, (orderNerveRealizationMap f f.monotone).hom.continuous⟩) :
    Whitehead.KillsPi2
      ⟨orderNerveRealizationMap (qposMap att f) (qposMap att f).monotone,
        (orderNerveRealizationMap (qposMap att f) (qposMap att f).monotone).hom.continuous⟩ := by
  letI : Nonempty Y := ⟨f x⟩
  apply killsPi2_qpos_of_base x hX (qpos_isConnected hY)
    (qposMap att f) (qposMap att f).monotone
  exact killsPi2_orderRealization_comp f f.monotone
    (qNew (A := A) (att := f.comp att)) qNew_monotone hk

end FiniteChains.Davis
