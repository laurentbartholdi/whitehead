import RequestProject.ChamberQuotientConnectedGeneration
import RequestProject.UniversalOrderDeckThree

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [Fintype V] {A : CommRel V}
variable {X R : Type} [PartialOrder X] [PartialOrder R] {att : NeSpx A →o X}

/-- Finite three-fillings of the images of base-cover cycles extend to images
of all chamber-cover cycles. The finite equivariant generation is proved by
the chamber construction, not supplied as an additional hypothesis. -/
theorem qCover_image_filling_of_base (x : X) (hX : IsConnected (orderCx X))
    (f : Qpos A X att → R) (hf : Monotone f)
    (hbase : ∀ c : UF (orderCx X) x →₀ ℤ,
      Comb.bdry2 (uCover (orderCx X) x) c = 0 →
        ∃ b : UOrdTet R (f (qNew x)) →₀ ℤ, uOrdBoundary3 b =
          chain2 (univLift (orderCx X)
            (orderCxMap (f ∘ qNew (A := A) (att := att)) (hf.comp qNew_monotone)) x) c)
    (z : UF (orderCx (Qpos A X att)) (qNew x) →₀ ℤ)
    (hz : Comb.bdry2 (uCover (orderCx (Qpos A X att)) (qNew x)) z = 0) :
    ∃ b : UOrdTet R (f (qNew x)) →₀ ℤ, uOrdBoundary3 b =
      chain2 (univLift (orderCx (Qpos A X att)) (orderCxMap f hf) (qNew x)) z := by
  classical
  obtain ⟨s, g, d, hd, y, he⟩ := exists_qCover_canonical_base_cycles_of_connected x hX z hz
  choose b hb using fun i => hbase (d i) (hd i)
  have ht (i) :
      chain2 (univLift (orderCx (Qpos A X att)) (orderCxMap f hf) (qNew x))
        (Finsupp.mapDomain (deckF (g i) ∘ univLiftF x
          (orderCxMap (qNew (A := A) (att := att)) qNew_monotone)) (d i)) =
      uOrdBoundary3 (Finsupp.mapDomain
        (deckUOrdTet (pi1Map (orderCxMap f hf) (qNew x) (g i))) (b i)) := by
    rw [Finsupp.mapDomain_comp]
    change chain2 (univLift (orderCx (Qpos A X att)) (orderCxMap f hf) (qNew x))
      (Finsupp.mapDomain (deckF (g i)) (chain2
        (univLift (orderCx X) (orderCxMap (qNew (A := A) (att := att)) qNew_monotone) x)
        (d i))) = _
    rw [univLift_chain2_deck]
    have hcomp :
        chain2 (univLift (orderCx (Qpos A X att)) (orderCxMap f hf) (qNew x))
          (chain2 (univLift (orderCx X)
            (orderCxMap (qNew (A := A) (att := att)) qNew_monotone) x) (d i)) =
        chain2 (univLift (orderCx X)
          (orderCxMap (f ∘ qNew (A := A) (att := att)) (hf.comp qNew_monotone)) x) (d i) :=
      univLift_chain2_comp (orderCxMap f hf)
        (orderCxMap (qNew (A := A) (att := att)) qNew_monotone) x (d i)
    rw [hcomp]
    change Finsupp.mapDomain (deckF (pi1Map (orderCxMap f hf) (qNew x) (g i)))
      (chain2 (univLift (orderCx X)
        (orderCxMap (f ∘ qNew (A := A) (att := att)) (hf.comp qNew_monotone)) x) (d i)) = _
    rw [← hb i]
    exact deck_uOrdBoundary3 (P := R) (a := f (qNew x))
      (pi1Map (orderCxMap f hf) (qNew x) (g i)) (b i)
  let B (i) : UOrdTet R (f (qNew x)) →₀ ℤ := Finsupp.mapDomain
    (deckUOrdTet (pi1Map (orderCxMap f hf) (qNew x) (g i))) (b i)
  let C : UOrdTet R (f (qNew x)) →₀ ℤ :=
    Finsupp.mapDomain (uOrdTetMap f hf (qNew x)) y
  refine ⟨(∑ i ∈ s, B i) + C, ?_⟩
  rw [he]
  simp only [B, C, map_add, map_sum, univLift_uOrdBoundary3]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => (ht i).symm)

end FiniteChains.Davis
