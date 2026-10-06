import RequestProject.PresCanonicalWords
import RequestProject.PresValidFinite
import RequestProject.OrderNerveEmbeddingCells

namespace FiniteChains.PresModel.PresWordEmbedding
open Comb Topology
variable {α β γ J K L : Type}
variable {w : J → List (α × Bool)} {v : K → List (β × Bool)}
  {z : L → List (γ × Bool)} (h : PresWordEmbedding w v)

/-- The actual continuous map induced by the given labelled word inclusion. -/
noncomputable def validRealizationMap :
    C(orderNerveRealization (ValidPresPos w), orderNerveRealization (ValidPresPos v)) :=
  ⟨orderNerveRealizationMap h.validMap h.validMap.monotone,
    (orderNerveRealizationMap h.validMap h.validMap.monotone).hom.continuous⟩

theorem validRealizationMap_trans (k : PresWordEmbedding v z) :
    (h.trans k).validRealizationMap = k.validRealizationMap.comp h.validRealizationMap := by
  apply ContinuousMap.ext
  intro x
  change orderNerveRealizationMap (h.trans k).validMap _ x =
    orderNerveRealizationMap k.validMap _ (orderNerveRealizationMap h.validMap _ x)
  rw [orderNerveRealizationMap_comp]
  have he : (k.validMap ∘ h.validMap : ValidPresPos w → ValidPresPos z) =
      (h.trans k).validMap := funext (fun p => (h.validMap_trans k p).symm)
  simp only [he]

theorem validRealizationMap_refl :
    (refl w).validRealizationMap = ContinuousMap.id (orderNerveRealization (ValidPresPos w)) := by
  apply ContinuousMap.ext
  intro x
  change orderNerveRealizationMap (refl w).validMap _ x = x
  have he : ((refl w).validMap : ValidPresPos w → ValidPresPos w) = id :=
    funext validMap_refl
  simp only [he, orderNerveRealizationMap_id]

/-- This is a Mathlib CW subcomplex of the actual target realization. -/
noncomputable def validSubcomplex :
    CWComplex.Subcomplex (Set.univ : Set (orderNerveRealization (ValidPresPos v))) :=
  orderNerveRealizationSubcomplex (ValidPresPos v) (Set.range h.validMap)

noncomputable def validHomeomorph : orderNerveRealization (ValidPresPos w) ≃ₜ
    (h.validSubcomplex : Set (orderNerveRealization (ValidPresPos v))) :=
  orderNerveRealizationEmbeddingHomeomorph h.validMap

theorem validHomeomorph_coe (x : orderNerveRealization (ValidPresPos w)) :
    (h.validHomeomorph x).val = h.validRealizationMap x :=
  orderNerveRealizationEmbeddingHomeomorph_coe h.validMap x

/-- The homeomorphism identifies the original open cells, as required in Challenge. -/
theorem valid_initialIdentification (hw : ∀ j, w j ≠ []) (hv : ∀ k, v k ≠ []) :
    @Whitehead.InitialIdentification (validPresTwoComplex w hw) (validPresTwoComplex v hv)
      h.validSubcomplex h.validHomeomorph :=
  orderNerveRealizationEmbedding_initialIdentification h.validMap
    (validPresPos_isConnected w hw) (validPresPos_isConnected v hv)

theorem valid_mid_not_mem_range {b : β} (hb : b ∉ Set.range h.gen) :
    (⟨iRose v (.mid b), trivial⟩ : ValidPresPos v) ∉ Set.range h.validMap := by
  rintro ⟨⟨p, hp⟩, he⟩
  have he' := congrArg Subtype.val he
  change h.posFun p = iRose v (.mid b) at he'
  cases p with
  | inr j => cases he'
  | inl p =>
    cases p with
    | inr c => cases he'
    | inl r =>
      cases r with
      | base => cases he'
      | edg a s => cases he'
      | mid a =>
        exact hb ⟨a, Rose.mid.inj (Sum.inl.inj (Sum.inl.inj he'))⟩

theorem valid_apex_not_mem_range {k : K} (hk : k ∉ Set.range h.cell) :
    (⟨apexOf v k, trivial⟩ : ValidPresPos v) ∉ Set.range h.validMap := by
  rintro ⟨⟨p, hp⟩, he⟩
  have he' := congrArg Subtype.val he
  change h.posFun p = apexOf v k at he'
  cases p with
  | inr j => exact hk ⟨j, Sum.inr.inj he'⟩
  | inl p => cases p <;> cases he'

/-- Adding a generator really gives a proper actual CW subcomplex. -/
theorem validSubcomplex_ne_univ_of_new_generator {b : β} (hb : b ∉ Set.range h.gen) :
    (h.validSubcomplex : Set (orderNerveRealization (ValidPresPos v))) ≠ Set.univ := by
  intro he
  have hx : orderNerveRealizationVertex (⟨iRose v (.mid b), trivial⟩ : ValidPresPos v) ∈
      (h.validSubcomplex : Set (orderNerveRealization (ValidPresPos v))) := by
    rw [he]
    trivial
  exact h.valid_mid_not_mem_range hb
    ((orderNerveRealizationVertex_mem_subcomplex _ _).mp hx)

/-- Adding a relator label likewise gives a proper actual CW subcomplex. -/
theorem validSubcomplex_ne_univ_of_new_relator {k : K} (hk : k ∉ Set.range h.cell) :
    (h.validSubcomplex : Set (orderNerveRealization (ValidPresPos v))) ≠ Set.univ := by
  intro he
  have hx : orderNerveRealizationVertex (⟨apexOf v k, trivial⟩ : ValidPresPos v) ∈
      (h.validSubcomplex : Set (orderNerveRealization (ValidPresPos v))) := by
    rw [he]
    trivial
  exact h.valid_apex_not_mem_range hk
    ((orderNerveRealizationVertex_mem_subcomplex _ _).mp hx)

end FiniteChains.PresModel.PresWordEmbedding
