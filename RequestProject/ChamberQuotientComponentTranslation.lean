import RequestProject.ChamberQuotientBaseDeck
import RequestProject.OrderSubposetChains

/-! Translate actual component cycles into the chosen lifted base component. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X} {a : Qpos A X att}
  (b r : QLiftedBase a) (g : Pi1 (orderCx (Qpos A X att)) a)
  (hg : Reach (orderCx (QLiftedBase a)) (qBaseDeckOrderIso g b) r)

noncomputable def qBaseTranslateToChosen (v : QBaseComponent a r) : QBaseComponent a b :=
  ⟨(qBaseDeckOrderIso g).symm v.1, by
    obtain ⟨p, hp⟩ := v.2
    have h := (hg.trans_path hp).map
      (orderCxMap (qBaseDeckOrderIso g).symm (qBaseDeckOrderIso g).symm.monotone)
    change Reach (orderCx (QLiftedBase a))
      ((qBaseDeckOrderIso g).symm ((qBaseDeckOrderIso g) b))
      ((qBaseDeckOrderIso g).symm v.1) at h
    simpa only [OrderIso.symm_apply_apply] using h⟩

omit [Fintype V] in
theorem qBaseTranslateToChosen_monotone : Monotone (qBaseTranslateToChosen b r g hg) :=
  fun _ _ h => (qBaseDeckOrderIso g).symm.monotone h

noncomputable def qBaseTranslateCx : Hom (orderCx (QBaseComponent a r)) (orderCx (QBaseComponent a b)) :=
  orderCxMap (qBaseTranslateToChosen b r g hg) (qBaseTranslateToChosen_monotone b r g hg)

noncomputable def qBaseChosenDeckTriangleMap : OrdTri (QBaseComponent a b) → OrdTri (QLiftedBase a) :=
  fun t => ⟨(qBaseDeckOrderIso g t.1.1.1, qBaseDeckOrderIso g t.1.2.1.1,
    qBaseDeckOrderIso g t.1.2.2.1), (qBaseDeckOrderIso g).monotone t.2.1,
    (qBaseDeckOrderIso g).monotone t.2.2⟩

omit [Fintype V] in
theorem qBaseTranslate_triangle_reinsert (t : OrdTri (QBaseComponent a r)) :
    qBaseChosenDeckTriangleMap b g ((qBaseTranslateCx b r g hg).onF t) =
      (ordSubposetIncl {v : QLiftedBase a | Reach (orderCx (QLiftedBase a)) r v}).onF t := by
  apply Subtype.ext
  exact Prod.ext ((qBaseDeckOrderIso g).apply_symm_apply t.1.1.1)
    (Prod.ext ((qBaseDeckOrderIso g).apply_symm_apply t.1.2.1.1)
      ((qBaseDeckOrderIso g).apply_symm_apply t.1.2.2.1))

omit [Fintype V] in
theorem qBaseTranslate_chain_reinsert (c : OrdTri (QBaseComponent a r) →₀ ℤ) :
    Finsupp.mapDomain (qBaseChosenDeckTriangleMap b g) (chain2 (qBaseTranslateCx b r g hg) c) =
      chain2 (ordSubposetIncl {v : QLiftedBase a | Reach (orderCx (QLiftedBase a)) r v}) c := by
  change Finsupp.mapDomain (qBaseChosenDeckTriangleMap b g)
    (Finsupp.mapDomain (qBaseTranslateCx b r g hg).onF c) = Finsupp.mapDomain _ c
  rw [← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro t _
  exact qBaseTranslate_triangle_reinsert b r g hg t

variable (hc : IsConnected (orderCx (Qpos A X att))) (hx : IsConnected (orderCx X))

noncomputable def qBaseUniversalTriangleMap :
    UF (orderCx X) (qBaseCoverEnd (X := X) a b) → OrdTri (QBaseComponent a b) :=
  (qBaseComponentUniversalHom a hc hx b).onF

noncomputable def qBaseDeckCycleFaceMap :
    UF (orderCx X) (qBaseCoverEnd (X := X) a b) → OrdTri (QLiftedBase a) :=
  qBaseChosenDeckTriangleMap b g ∘ qBaseUniversalTriangleMap b hc hx

include hg in
theorem exists_qBase_chosen_cycle_of_component
    (c : OrdTri (QBaseComponent a r) →₀ ℤ)
    (hcyc : Comb.bdry2 (orderCx (QBaseComponent a r)) c = 0) :
    ∃ d : UF (orderCx X) (qBaseCoverEnd (X := X) a b) →₀ ℤ,
      Comb.bdry2 (uCover (orderCx X) (qBaseCoverEnd (X := X) a b)) d = 0 ∧
      Finsupp.mapDomain (qBaseDeckCycleFaceMap b g hc hx) d =
        chain2 (ordSubposetIncl {v : QLiftedBase a | Reach (orderCx (QLiftedBase a)) r v}) c := by
  have htc : Comb.bdry2 (orderCx (QBaseComponent a b))
      (chain2 (qBaseTranslateCx b r g hg) c) = 0 := by
    rw [bdry2_chain2, hcyc, map_zero]
  obtain ⟨d, ⟨hd, hdc⟩, _⟩ := exists_unique_qBaseComponent_cycle a hc hx b _ htc
  refine ⟨d, hdc, ?_⟩
  change Finsupp.mapDomain (qBaseChosenDeckTriangleMap b g ∘
    (qBaseComponentUniversalHom a hc hx b).onF) d = _
  rw [Finsupp.mapDomain_comp]
  change Finsupp.mapDomain (qBaseChosenDeckTriangleMap b g)
    (chain2 (qBaseComponentUniversalHom a hc hx b) d) = _
  rw [hd]
  exact qBaseTranslate_chain_reinsert b r g hg c

end FiniteChains.Davis
