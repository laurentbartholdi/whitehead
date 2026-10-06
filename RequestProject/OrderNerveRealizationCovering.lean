import RequestProject.OrderNerveRealizationStarSheets
import Mathlib.Topology.Covering.Basic

/-! Actual topological coverings obtained from the already constructed open-star sheets. -/

namespace FiniteChains.Comb
open Topology
open scoped Classical

private theorem open_iff_of_sheet {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X] (f : C(E, X))
    {U : Set E} {V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (e : U ≃ₜ V) (he : ∀ z : U, (e z).val = f z.val)
    {W : Set X} (hW : W ⊆ V) :
    IsOpen W ↔ IsOpen (f ⁻¹' W ∩ U) := by
  constructor
  · intro h
    exact (h.preimage f.continuous).inter hU
  · intro h
    have hp : IsOpen (e ⁻¹' ((Subtype.val : V → X) ⁻¹' W)) := by
      have hh := h.preimage (continuous_subtype_val : Continuous (Subtype.val : U → E))
      convert hh using 1
      ext z
      change (e z).val ∈ W ↔ f z.val ∈ W ∧ z.val ∈ U
      rw [he z]
      simp only [z.property, and_true]
    have hv := e.isOpen_preimage.mp hp
    have hi := hV.isOpenMap_subtype_val _ hv
    have hr : (Subtype.val : V → X) '' (Subtype.val ⁻¹' W) = W := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hx
        exact ⟨⟨x, hW hx⟩, hx, rfl⟩
    rwa [hr] at hi

namespace IsPosetCover
variable {P Q : Type} [PartialOrder P] [PartialOrder Q] {f : P → Q}

/-- A sheet over a chosen lifted vertex, with its target identified with the chosen base star. -/
noncomputable def realizationSheetHomeomorph (hf : IsPosetCover f) (q : Q)
    (v : {p : P // f p = q}) :
    orderNerveRealizationOpenStar P v.val ≃ₜ orderNerveRealizationOpenStar Q q :=
  (hf.vertexOpenStarHomeomorph v.val).trans
    (Homeomorph.setCongr (congrArg (orderNerveRealizationOpenStar Q) v.property))

theorem realizationSheetHomeomorph_coe (hf : IsPosetCover f) (q : Q)
    (v : {p : P // f p = q}) (z : orderNerveRealizationOpenStar P v.val) :
    (hf.realizationSheetHomeomorph q v z).val = orderNerveRealizationMap f hf.mono z.val :=
  hf.vertexOpenStarHomeomorph_coe v.val z

set_option maxHeartbeats 600000 in
/-- Every actual open vertex star is an evenly covered neighborhood. -/
theorem realizationMap_evenlyCovered (hf : IsPosetCover f) (q : Q)
    (x : orderNerveRealization Q) (hx : x ∈ orderNerveRealizationOpenStar Q q) :
    IsEvenlyCovered (orderNerveRealizationMap f hf.mono) x
      (orderNerveRealizationMap f hf.mono ⁻¹' {x}) := by
  let I := {p : P // f p = q}
  letI : TopologicalSpace I := ⊥
  letI : DiscreteTopology I := ⟨rfl⟩
  obtain ⟨v, hv⟩ := hf.surj q
  letI : Nonempty I := ⟨⟨v, hv⟩⟩
  letI : Nonempty (orderNerveRealization P) := ⟨orderNerveRealizationVertex v⟩
  let F : C(orderNerveRealization P, orderNerveRealization Q) :=
    ⟨orderNerveRealizationMap f hf.mono, (orderNerveRealizationMap f hf.mono).hom.continuous⟩
  let U : I → Set (orderNerveRealization P) := fun i => orderNerveRealizationOpenStar P i.val
  let V := orderNerveRealizationOpenStar Q q
  let e : ∀ i : I, U i ≃ₜ V := hf.realizationSheetHomeomorph q
  have he : ∀ (i : I) (z : U i), (e i z).val = F z.val :=
    hf.realizationSheetHomeomorph_coe q
  let t := IsOpen.trivializationDiscrete (f := F) U V
    (orderNerveRealizationOpenStar_isOpen Q q)
    (fun i {_} hW => open_iff_of_sheet F (orderNerveRealizationOpenStar_isOpen P i.val)
      (orderNerveRealizationOpenStar_isOpen Q q) (e i) (he i) hW)
    (by
      intro i a ha b hb hab
      have hh : e i ⟨a, ha⟩ = e i ⟨b, hb⟩ :=
        Subtype.ext ((he i ⟨a, ha⟩).trans (hab.trans (he i ⟨b, hb⟩).symm))
      exact congrArg Subtype.val ((e i).injective hh))
    (by
      intro i y hy
      refine ⟨((e i).symm ⟨y, hy⟩).val, ((e i).symm ⟨y, hy⟩).property, ?_⟩
      rw [← he i, (e i).apply_symm_apply])
    (by
      intro i j hij
      exact hf.realizationOpenStar_disjoint (fun h => hij (Subtype.ext h))
        (i.property.trans j.property.symm))
    (by
      intro y hy
      obtain ⟨p, hp, hyp⟩ := (orderNerveRealizationMap_mem_openStar_iff f hf.mono y q).mp hy
      exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hyp⟩)
  exact (IsEvenlyCovered.of_trivialization (t := t) hx).to_isEvenlyCovered_preimage

/-- The realization of every poset covering is a genuine Mathlib covering map. -/
theorem realizationMap_isCoveringMap (hf : IsPosetCover f) :
    IsCoveringMap (orderNerveRealizationMap f hf.mono) := by
  intro x
  obtain ⟨q, hq⟩ := orderNerveRealizationOpenStar_cover Q x
  exact hf.realizationMap_evenlyCovered q x hq

end IsPosetCover
end FiniteChains.Comb
