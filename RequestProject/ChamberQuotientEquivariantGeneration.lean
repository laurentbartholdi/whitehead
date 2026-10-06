import RequestProject.ChamberQuotientChosenGeneration

/-! Actual quotient cycles are generated modulo genuine three-boundaries by
deck translates of genuine universal-cover cycles of the chosen base. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

def qLiftedBaseTriangleMap (a : Qpos A X att) :
    OrdTri (QLiftedBase a) → OrdTri (UOrder (Qpos A X att) a) :=
  fun t => ⟨(t.1.1.1, t.1.2.1.1, t.1.2.2.1), t.2⟩

def qLiftedBaseFaceMap (a : Qpos A X att) :
    OrdTri (QLiftedBase a) → UF (orderCx (Qpos A X att)) a :=
  uOrderFace ∘ qLiftedBaseTriangleMap a

noncomputable def qBaseDeckCoverFaceMap {a : Qpos A X att} (b : QLiftedBase a)
    (g : Pi1 (orderCx (Qpos A X att)) a)
    (hc : IsConnected (orderCx (Qpos A X att))) (hx : IsConnected (orderCx X)) :
    UF (orderCx X) (qBaseCoverEnd (X := X) a b) → UF (orderCx (Qpos A X att)) a :=
  qLiftedBaseFaceMap a ∘ qBaseDeckCycleFaceMap b g hc hx

theorem qpos_isConnected_of_zpos
    (hconn : IsConnected (orderCx (Zpos A X (IsGamma A) att))) :
    IsConnected (orderCx (Qpos A X att)) := by
  intro q r
  obtain ⟨v, hv⟩ := zProj_surjective (A := A) (X := X) (att := att) q
  obtain ⟨w, hw⟩ := zProj_surjective (A := A) (X := X) (att := att) r
  obtain ⟨l, hl⟩ := hconn v w
  let p := orderCxMap (zProj (A := A) (X := X) (att := att)) zProj_monotone
  have h := isPath_mapPath p hl
  change IsPath (orderCx (Qpos A X att)).src (orderCx (Qpos A X att)).tgt
    (mapPath p l) (zProj v) (zProj w) at h
  rw (config := { transparency := .default }) [hv, hw] at h
  exact ⟨mapPath p l, h⟩

omit [Fintype V] in
theorem exists_qCover_base_cycle_preimage {a : Qpos A X att}
    (c : UF (orderCx (Qpos A X att)) a →₀ ℤ)
    (hs : ∀ t ∈ c.support, InQBase t.1.2.1.1 ∧ InQBase t.1.2.1.2.1 ∧
      InQBase t.1.2.1.2.2)
    (hc : Comb.bdry2 (uCover (orderCx (Qpos A X att)) a) c = 0) :
    ∃ d : OrdTri (QLiftedBase a) →₀ ℤ,
      Comb.bdry2 (orderCx (QLiftedBase a)) d = 0 ∧
      Finsupp.mapDomain (qLiftedBaseFaceMap a) d = c := by
  classical
  obtain ⟨e, ⟨he, hecyc⟩, _⟩ := exists_unique_uOrder_cycle c hc
  have he' : Finsupp.mapDomain uOrderFace e = c := he
  let S : Set (UOrder (Qpos A X att) a) := {p | InQBase (uOrderEnd p)}
  have hes : ∀ t ∈ e.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S := by
    intro t ht
    have ht' : uOrderFace t ∈ c.support := by
      rw (config := { transparency := .default }) [← he', Finsupp.mapDomain_support_of_injective uOrderFace_injective]
      exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
    exact hs _ ht'
  obtain ⟨d, hd, hdcyc⟩ := exists_ordSubposet_cycle S e hes hecyc
  refine ⟨d, hdcyc, ?_⟩
  change Finsupp.mapDomain (uOrderFace ∘ (ordSubposetIncl S).onF) d = c
  rw (config := { transparency := .default }) [Finsupp.mapDomain_comp]
  change Finsupp.mapDomain uOrderFace (chain2 (ordSubposetIncl S) d) = c
  rw (config := { transparency := .default }) [hd, he']

variable [Nonempty X]

/-- Finite equivariant generation in the actual quotient model, with all source
cycles in the genuine universal cover of one fixed original-base point. -/
theorem exists_qCover_equivariant_base_cycles (a : Zpos A X (IsGamma A) att)
    (hconn : IsConnected (orderCx (Zpos A X (IsGamma A) att)))
    (hx : IsConnected (orderCx X)) (b : QLiftedBase (zProj a))
    (z : UF (orderCx (Qpos A X att)) (zProj a) →₀ ℤ)
    (hz : Comb.bdry2 (uCover (orderCx (Qpos A X att)) (zProj a)) z = 0) :
    ∃ (s : Finset (OrderComponent (QLiftedBase (zProj a))))
      (g : OrderComponent (QLiftedBase (zProj a)) → Pi1 (orderCx (Qpos A X att)) (zProj a))
      (d : OrderComponent (QLiftedBase (zProj a)) →
        (UF (orderCx X) (qBaseCoverEnd (X := X) (zProj a) b) →₀ ℤ)),
      (∀ i, Comb.bdry2 (uCover (orderCx X) (qBaseCoverEnd (X := X) (zProj a) b)) (d i) = 0) ∧
      ∃ y : UOrdTet (Qpos A X att) (zProj a) →₀ ℤ,
        z = (∑ i ∈ s, Finsupp.mapDomain
          (qBaseDeckCoverFaceMap b (g i) (qpos_isConnected_of_zpos hconn) hx) (d i)) +
            uOrdBoundary3 y := by
  classical
  obtain ⟨c, hs, hc, y, he⟩ := exists_qCover_base_cellular_cycle a hconn z hz
  obtain ⟨c', hc', hmap⟩ := exists_qCover_base_cycle_preimage c hs hc
  obtain ⟨s, g, d, hd, hsum⟩ := exists_qBase_deck_cycle_decomposition
    (qpos_isConnected_of_zpos hconn) hx b c' hc'
  refine ⟨s, g, d, hd, y, ?_⟩
  have hbase : c = ∑ i ∈ s, Finsupp.mapDomain
      (qBaseDeckCoverFaceMap b (g i) (qpos_isConnected_of_zpos hconn) hx) (d i) := by
    rw (config := { transparency := .default }) [← hmap, hsum]
    change (Finsupp.lmapDomain ℤ ℤ (qLiftedBaseFaceMap (zProj a)))
      (∑ i ∈ s, Finsupp.mapDomain
        (qBaseDeckCycleFaceMap b (g i) (qpos_isConnected_of_zpos hconn) hx) (d i)) = _
    rw (config := { transparency := .default }) [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (Finsupp.mapDomain_comp (v := d i)).symm
  rw (config := { transparency := .default }) [hbase] at he
  exact he

end FiniteChains.Davis
