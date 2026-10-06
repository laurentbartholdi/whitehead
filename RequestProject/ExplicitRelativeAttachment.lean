module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.ContinuousMap.Basic

@[expose] public section

/-! An explicit attachment space retaining every point of its base. The
base is proved to embed as a closed subspace when the boundary inclusion is
closed. This supplies the topological primitive before constructing the
classical CW characteristic maps. Pending Lean verification.
-/

noncomputable section
open scoped Classical
open Set Topology TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.RelativeAttachment

universe u
variable {A X D : Type u}

/-- The old points and the interior points are distinct summands. The base
map is retained in the type because it determines the attachment topology. -/
def Space (_r : A → X) (i : A → D) : Type u :=
  X ⊕ {d : D // d ∉ Set.range i}

def old (r : A → X) (i : A → D) : X → Space r i := Sum.inl

def cell (r : A → X) (i : A → D) (d : D) : Space r i :=
  if h : d ∈ Set.range i then Sum.inl (r (Classical.choose h))
  else Sum.inr ⟨d, h⟩

def quotientMap (r : A → X) (i : A → D) : X ⊕ D → Space r i :=
  Sum.elim (old r i) (cell r i)

/-- The genuinely added interior points. -/
def fresh (r : A → X) (i : A → D) : {d : D // d ∉ Set.range i} → Space r i :=
  Sum.inr

theorem old_injective (r : A → X) (i : A → D) : Function.Injective (old r i) :=
  Sum.inl_injective

@[simp] theorem cell_of_not_mem (r : A → X) (i : A → D) (d : D)
    (hd : d ∉ Set.range i) : cell r i d = Sum.inr ⟨d, hd⟩ := by
  unfold cell
  rw [dite_eq_right hd]

theorem cell_boundary (r : A → X) (i : A → D) (hi : Function.Injective i) (a : A) :
    cell r i (i a) = old r i (r a) := by
  have h : i a ∈ Set.range i := ⟨a, rfl⟩
  simp only [cell, old]
  rw [dite_eq_left h]
  exact congrArg Sum.inl (congrArg r (hi (Classical.choose_spec h)))

theorem quotientMap_surjective (r : A → X) (i : A → D) :
    Function.Surjective (quotientMap r i) := by
  rintro (x | d)
  · exact ⟨Sum.inl x, rfl⟩
  · exact ⟨Sum.inr d.val, cell_of_not_mem r i d.val d.property⟩

variable [TopologicalSpace X] [TopologicalSpace D]

/-- The topology is exactly the quotient topology for adjoining the disks
along their boundaries; it is not the disjoint-sum topology on `Space`. -/
instance topology (r : A → X) (i : A → D) : TopologicalSpace (Space r i) :=
  TopologicalSpace.coinduced (quotientMap r i) inferInstance

theorem quotientMap_continuous (r : A → X) (i : A → D) :
    Continuous (quotientMap r i) := continuous_coinduced_rng

theorem old_continuous (r : A → X) (i : A → D) : Continuous (old r i) :=
  (quotientMap_continuous r i).comp continuous_inl

theorem cell_continuous (r : A → X) (i : A → D) : Continuous (cell r i) :=
  (quotientMap_continuous r i).comp continuous_inr

theorem fresh_continuous (r : A → X) (i : A → D) : Continuous (fresh r i) := by
  have he : fresh r i = cell r i ∘ Subtype.val := by
    funext d
    exact (cell_of_not_mem r i d.val d.property).symm
  rw [he]
  exact (cell_continuous r i).comp continuous_subtype_val

omit [TopologicalSpace X] [TopologicalSpace D] in
theorem old_preimage_fresh_image (r : A → X) (i : A → D)
    (S : Set {d : D // d ∉ Set.range i}) :
    (old r i) ⁻¹' ((fresh r i) '' S) = ∅ := by
  ext x
  constructor
  · rintro ⟨d, _, he⟩
    exact Sum.inr_ne_inl he
  · exact False.elim

omit [TopologicalSpace X] [TopologicalSpace D] in
theorem cell_preimage_fresh_image (r : A → X) (i : A → D)
    (S : Set {d : D // d ∉ Set.range i}) :
    (cell r i) ⁻¹' ((fresh r i) '' S) = Subtype.val '' S := by
  ext d
  constructor
  · rintro ⟨v, hv, he⟩
    by_cases hd : d ∈ Set.range i
    · have he' : Sum.inr v = Sum.inl (r (Classical.choose hd)) := by
        simp only [fresh, cell] at he
        rw [dite_eq_left hd] at he
        exact he
      exact (Sum.inr_ne_inl he').elim
    · have hvd : v = ⟨d, hd⟩ := by
        apply Sum.inr_injective
        simp only [fresh, cell] at he
        rw [dite_eq_right hd] at he
        exact he
      exact ⟨v, hv, congrArg Subtype.val hvd⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, (cell_of_not_mem r i v.val v.property).symm⟩

/-- The new interiors have their original topology and form an open subset
of the attachment whenever the boundary is closed. -/
theorem fresh_isOpenEmbedding (r : A → X) (i : A → D)
    (hi : IsClosed (Set.range i)) : IsOpenEmbedding (fresh r i) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
    (fresh_continuous r i) Sum.inr_injective
  intro S hS
  apply isOpen_coinduced.mpr
  apply isOpen_sum_iff.mpr
  constructor
  · change IsOpen ((old r i) ⁻¹' ((fresh r i) '' S))
    rw [old_preimage_fresh_image]
    exact isOpen_empty
  · change IsOpen ((cell r i) ⁻¹' ((fresh r i) '' S))
    rw [cell_preimage_fresh_image]
    exact hi.isOpen_compl.isOpenEmbedding_subtypeVal.isOpenMap _ hS

omit [TopologicalSpace X] [TopologicalSpace D] in
theorem old_fresh_disjoint (r : A → X) (i : A → D) :
    Disjoint (Set.range (old r i)) (Set.range (fresh r i)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, rfl⟩ ⟨d, hd⟩
  exact Sum.inr_ne_inl hd

omit [TopologicalSpace X] [TopologicalSpace D] in
theorem old_union_fresh (r : A → X) (i : A → D) :
    Set.range (old r i) ∪ Set.range (fresh r i) = Set.univ := by
  apply Set.eq_univ_of_forall
  rintro (x | d)
  · exact Or.inl ⟨x, rfl⟩
  · exact Or.inr ⟨d, rfl⟩

variable {Z : Type u} [TopologicalSpace Z]

def descFun (r : A → X) (i : A → D) (f : C(X, Z)) (g : C(D, Z)) :
    Space r i → Z := Sum.elim f (fun d => g d.val)

theorem descFun_cell (r : A → X) (i : A → D) (f : C(X, Z)) (g : C(D, Z))
    (h : ∀ a, f (r a) = g (i a)) (d : D) : descFun r i f g (cell r i d) = g d := by
  simp only [cell, descFun]
  split_ifs with hd
  · simp only [Sum.elim_inl]; rw [h, Classical.choose_spec hd]
  · simp only [Sum.elim_inr]

/-- The actual continuous pushout map determined by compatible maps on the
base and the disks. -/
def desc (r : A → X) (i : A → D) (f : C(X, Z)) (g : C(D, Z))
    (h : ∀ a, f (r a) = g (i a)) : C(Space r i, Z) where
  toFun := descFun r i f g
  continuous_toFun := by
    apply continuous_coinduced_dom.mpr
    have he : descFun r i f g ∘ quotientMap r i = Sum.elim f g := by
      funext z
      cases z with
      | inl x => rfl
      | inr d => exact descFun_cell r i f g h d
    rw [he]
    exact f.continuous.sumElim g.continuous

@[simp] theorem desc_old (r : A → X) (i : A → D) (f : C(X, Z)) (g : C(D, Z))
    (h : ∀ a, f (r a) = g (i a)) (x : X) : desc r i f g h (old r i x) = f x := rfl

@[simp] theorem desc_cell (r : A → X) (i : A → D) (f : C(X, Z)) (g : C(D, Z))
    (h : ∀ a, f (r a) = g (i a)) (d : D) : desc r i f g h (cell r i d) = g d :=
  descFun_cell r i f g h d

theorem hom_ext (r : A → X) (i : A → D) {f g : C(Space r i, Z)}
    (hOld : ∀ x, f (old r i x) = g (old r i x))
    (hCell : ∀ d, f (cell r i d) = g (cell r i d)) : f = g := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨z, rfl⟩ := quotientMap_surjective r i z
  cases z with
  | inl x => exact hOld x
  | inr d => exact hCell d

variable [TopologicalSpace A]

omit [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace D] in
/-- Pulling an old subset back to the disks gives exactly its attached
boundary points. No old point is identified with another old point. -/
theorem cell_preimage_old_image (r : A → X) (i : A → D)
    (hi : Function.Injective i) (S : Set X) :
    (cell r i) ⁻¹' ((old r i) '' S) = i '' (r ⁻¹' S) := by
  ext d
  constructor
  · rintro ⟨x, hx, he⟩
    by_cases hd : d ∈ Set.range i
    · refine ⟨Classical.choose hd, ?_, Classical.choose_spec hd⟩
      have hr : x = r (Classical.choose hd) := by
        apply Sum.inl_injective
        simp only [old, cell] at he
        rw [dite_eq_left hd] at he
        exact he
      change r (Classical.choose hd) ∈ S
      rwa [← hr]
    · have he' := he
      rw [cell_of_not_mem r i d hd] at he'
      exact (Sum.inl_ne_inr he').elim
  · rintro ⟨a, ha, rfl⟩
    exact ⟨r a, ha, (cell_boundary r i hi a).symm⟩

/-- The literal original space embeds as a closed subspace of the actual
attachment, provided the boundary inclusion is a closed embedding. -/
theorem old_isClosedEmbedding (r : A → X) (i : A → D)
    (hr : Continuous r) (hi : IsClosedEmbedding i) : IsClosedEmbedding (old r i) := by
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap
    (old_continuous r i) (old_injective r i)
  intro S hS
  apply isClosed_coinduced.mpr
  apply isClosed_sum_iff.mpr
  constructor
  · change IsClosed ((old r i) ⁻¹' ((old r i) '' S))
    rw [Set.preimage_image_eq S (old_injective r i)]
    exact hS
  · change IsClosed ((cell r i) ⁻¹' ((old r i) '' S))
    rw [cell_preimage_old_image r i hi.injective]
    exact hi.isClosedMap _ (hS.preimage hr)

/-- This homeomorphism uses the original points of the given base. -/
def oldHomeomorph (r : A → X) (i : A → D)
    (hr : Continuous r) (hi : IsClosedEmbedding i) :
    X ≃ₜ Set.range (old r i) :=
  (old_isClosedEmbedding r i hr hi).isEmbedding.toHomeomorph

end FiniteChains.RelativeAttachment
