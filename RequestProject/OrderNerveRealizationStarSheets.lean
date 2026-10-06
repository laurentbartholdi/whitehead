module

public import RequestProject.OrderNerveRealizationOpenStars

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical
/-- Viewing a subset inside a containing carrier preserves its actual subspace topology. -/
def orderNerveNestedCarrierHomeomorph {X : Type} [TopologicalSpace X]
    (S C : Set X) (h : S ⊆ C) : S ≃ₜ {x : C // x.val ∈ S} where
  toFun x := ⟨⟨x.val, h x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

namespace IsPosetCover
variable {P Q : Type} [PartialOrder P] [PartialOrder Q] {f : P → Q}

/-- The actual supported closed-star carriers are homeomorphic under a poset cover. -/
noncomputable def vertexStarCarrierHomeomorph (hf : IsPosetCover f) (v : P) :
    (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v) :
      Set (orderNerveRealization P)) ≃ₜ
    (orderNerveRealizationSubcomplex Q (orderNerveVertexStar Q (f v)) :
      Set (orderNerveRealization Q)) :=
  (orderNerveRealizationSubtypeHomeomorph (orderNerveVertexStar P v)).symm.trans
    ((hf.vertexStarRealizationHomeomorph v).trans
      (orderNerveRealizationSubtypeHomeomorph (orderNerveVertexStar Q (f v))))

/-- The closed-star carrier homeomorphism agrees with the actual realized projection. -/
theorem vertexStarCarrierHomeomorph_coe (hf : IsPosetCover f) (v : P)
    (x : (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v) :
      Set (orderNerveRealization P))) :
    (hf.vertexStarCarrierHomeomorph v x).val = orderNerveRealizationMap f hf.mono x.val := by
  obtain ⟨y, rfl⟩ := (orderNerveRealizationSubtypeHomeomorph
    (orderNerveVertexStar P v)).surjective x
  change (orderNerveRealizationSubtypeHomeomorph (orderNerveVertexStar Q (f v))
    (hf.vertexStarRealizationHomeomorph v
      ((orderNerveRealizationSubtypeHomeomorph (orderNerveVertexStar P v)).symm
        (orderNerveRealizationSubtypeHomeomorph (orderNerveVertexStar P v) y)))).val = _
  rw (config := { transparency := .default }) [Homeomorph.symm_apply_apply, orderNerveRealizationSubtypeHomeomorph_coe,
    orderNerveRealizationSubtypeHomeomorph_coe]
  change orderNerveRealizationMap (Subtype.val : orderNerveVertexStar Q (f v) → Q)
      (fun _ _ h => h) (orderNerveRealizationMap (hf.vertexStarMap v) _ y) =
    orderNerveRealizationMap f hf.mono
      (orderNerveRealizationMap (Subtype.val : orderNerveVertexStar P v → P)
        (fun _ _ h => h) y)
  rw (config := { transparency := .default }) [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
  rfl

/-- On a lifted closed star, the center coordinate is preserved by the projection. -/
theorem vertexStarCarrier_coordinate (hf : IsPosetCover f) (v : P)
    (x : (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v) :
      Set (orderNerveRealization P))) :
    orderNerveRealizationCoordinates Q (orderNerveRealizationMap f hf.mono x.val) (f v) =
      orderNerveRealizationCoordinates P x.val v := by
  obtain ⟨y, rfl⟩ := (orderNerveRealizationSubtypeHomeomorph
    (orderNerveVertexStar P v)).surjective x
  rw (config := { transparency := .default }) [orderNerveRealizationSubtypeHomeomorph_coe]
  change orderNerveAffineRealization (fun q => if q = f v then 1 else 0)
    (orderNerveRealizationMap f hf.mono
      (orderNerveRealizationMap Subtype.val (fun _ _ h => h) y)) =
    orderNerveAffineRealization (fun p => if p = v then 1 else 0)
      (orderNerveRealizationMap Subtype.val (fun _ _ h => h) y)
  rw (config := { transparency := .default }) [orderNerveAffineRealization_natural, orderNerveAffineRealization_natural,
    orderNerveAffineRealization_natural]
  have hv : (((fun q => if q = f v then (1 : ℝ) else 0) ∘ f) ∘
      (Subtype.val : orderNerveVertexStar P v → P)) =
      ((fun p => if p = v then (1 : ℝ) else 0) ∘ Subtype.val) := by
    funext p
    have he : f p.val = f v ↔ p.val = v := by
      constructor
      · intro h
        rcases p.property with hp | hp
        · exact hf.down_inj hp (le_refl v) h
        · exact hf.up_inj hp (le_refl v) h
      · intro h
        exact congrArg f h
    simp only [Function.comp_apply, he]
  rw (config := { transparency := .default }) [hv]

/-- Each lifted open star is genuinely homeomorphic to its target open star. -/
noncomputable def vertexOpenStarHomeomorph (hf : IsPosetCover f) (v : P) :
    orderNerveRealizationOpenStar P v ≃ₜ orderNerveRealizationOpenStar Q (f v) :=
  (orderNerveNestedCarrierHomeomorph _ _
    (orderNerveRealizationOpenStar_subset_subcomplex v)).trans
    (((hf.vertexStarCarrierHomeomorph v).subtype (p := fun x =>
      x.val ∈ orderNerveRealizationOpenStar P v) (q := fun x =>
      x.val ∈ orderNerveRealizationOpenStar Q (f v)) (by
        intro x
        change (0 < orderNerveRealizationCoordinates P x.val v) ↔
          (0 < orderNerveRealizationCoordinates Q
            (hf.vertexStarCarrierHomeomorph v x).val (f v))
        rw (config := { transparency := .default }) [hf.vertexStarCarrierHomeomorph_coe, hf.vertexStarCarrier_coordinate])).trans
      (orderNerveNestedCarrierHomeomorph _ _
        (orderNerveRealizationOpenStar_subset_subcomplex (f v))).symm)

/-- The open-sheet homeomorphism is the actual realized projection. -/
theorem vertexOpenStarHomeomorph_coe (hf : IsPosetCover f) (v : P)
    (x : orderNerveRealizationOpenStar P v) :
    (hf.vertexOpenStarHomeomorph v x).val = orderNerveRealizationMap f hf.mono x.val := by
  exact hf.vertexStarCarrierHomeomorph_coe v
    ⟨x.val, orderNerveRealizationOpenStar_subset_subcomplex v x.property⟩

end IsPosetCover
end FiniteChains.Comb
