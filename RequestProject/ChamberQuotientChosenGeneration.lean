import RequestProject.ChamberQuotientComponentTranslation
import RequestProject.OrderLabelCycleDecomposition

/-! Actual finite generation of lifted base cycles by deck translates of the
genuine universal-cover cycles of one chosen base component. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X} {a : Qpos A X att}

theorem exists_qBase_deck_cycle_decomposition
    (hc : IsConnected (orderCx (Qpos A X att))) (hx : IsConnected (orderCx X))
    (b : QLiftedBase a) (c : OrdTri (QLiftedBase a) →₀ ℤ)
    (hcyc : Comb.bdry2 (orderCx (QLiftedBase a)) c = 0) :
    ∃ (s : Finset (OrderComponent (QLiftedBase a)))
      (g : OrderComponent (QLiftedBase a) → Pi1 (orderCx (Qpos A X att)) a)
      (d : OrderComponent (QLiftedBase a) →
        (UF (orderCx X) (qBaseCoverEnd (X := X) a b) →₀ ℤ)),
      (∀ i, Comb.bdry2 (uCover (orderCx X) (qBaseCoverEnd (X := X) a b)) (d i) = 0) ∧
      c = ∑ i ∈ s, Finsupp.mapDomain (qBaseDeckCycleFaceMap b (g i) hc hx) (d i) := by
  classical
  obtain ⟨s, parts, hparts, hsupport, hsum⟩ := exists_ord_label_cycle_decomposition
    (orderComponentLabel (QLiftedBase a)) (fun {_ _} h => orderComponentLabel_eq_of_le h) c hcyc
  let r : OrderComponent (QLiftedBase a) → QLiftedBase a := Quotient.out
  have hr : ∀ i, orderComponentLabel (QLiftedBase a) (r i) = i := fun i => Quotient.out_eq i
  have hpiece : ∀ i : OrderComponent (QLiftedBase a),
      ∃ (g : Pi1 (orderCx (Qpos A X att)) a)
        (d : UF (orderCx X) (qBaseCoverEnd (X := X) a b) →₀ ℤ),
        Comb.bdry2 (uCover (orderCx X) (qBaseCoverEnd (X := X) a b)) d = 0 ∧
        Finsupp.mapDomain (qBaseDeckCycleFaceMap b g hc hx) d = parts i := by
    intro i
    let S : Set (QLiftedBase a) := {v | Reach (orderCx (QLiftedBase a)) (r i) v}
    have hs : ∀ t ∈ (parts i).support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S := by
      intro t ht
      obtain ⟨h₀, h₁, h₂⟩ := hsupport i t ht
      exact ⟨(orderComponentLabel_eq_iff _ _).mp ((hr i).trans h₀.symm),
        (orderComponentLabel_eq_iff _ _).mp ((hr i).trans h₁.symm),
        (orderComponentLabel_eq_iff _ _).mp ((hr i).trans h₂.symm)⟩
    obtain ⟨u, hu, hucyc⟩ := exists_ordSubposet_cycle S (parts i) hs (hparts i)
    obtain ⟨g, hg⟩ := qBase_components_deck_transitive hc hx b (r i)
    obtain ⟨d, hdc, hd⟩ := exists_qBase_chosen_cycle_of_component b (r i) g hg hc hx u hucyc
    exact ⟨g, d, hdc, hd.trans hu⟩
  choose g d hd hmap using hpiece
  refine ⟨s, g, d, hd, ?_⟩
  simp_rw [hmap]
  exact hsum

end FiniteChains.Davis
