import RequestProject.CockcroftExtStep

/-!
# Subpresentations that are retracts: their Fox cycles have zero augmentation

This file isolates the mechanism behind the last step of Lemma 3.10 ("a wedge of Cockcroft
complexes is Cockcroft: the factor retractions detect every coordinate of a Hurewicz image").

Suppose a presentation `τ` contains a presentation `ρ` as a *block*: the generators and the
relators of `ρ` sit inside those of `τ` (injectively, and old relators are read as the same
words), no relator outside the block involves a generator of the block, and there is a
retraction of the ambient free group onto the free group of the block which carries the
relators of `τ` into the relator subgroup of `ρ`.  Then every Fox cycle of `τ` has, in the
coordinates of the block, zero augmentation as soon as `ρ` is Cockcroft
(`FiniteChains.augPres_block_eq_zero`).

The proof is the one used throughout Section 3.4: the block equations say that the block
coordinates form a cycle of the Fox matrix of `ρ`, read in the group ring of the image of
`π₁` of the block; that image is a faithful copy of `π₁` of the block because of the
retraction, so the base change statement of `RequestProject/BaseChangeCycles.lean` writes the
block coordinates as a combination of images of Fox cycles of `ρ`, whose augmentations vanish.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

universe u

variable {α γ : Type u} [DecidableEq γ]
variable {J L : Type u}
variable (ρ : J → FreeGroup α) (τ : L → FreeGroup γ) (f : α → γ) (g : J → L)
variable (r : FreeGroup γ →* FreeGroup α)

/-- The data expressing that the presentation `ρ` is a retract block of the presentation `τ`.
-/
structure IsBlock : Prop where
  /-- the generators of the block are included injectively -/
  gen_injective : Function.Injective f
  /-- the two-cells of the block are included injectively -/
  cell_injective : Function.Injective g
  /-- an old relator is read as the same word -/
  rel_eq : ∀ j, τ (g j) = FreeGroup.map f (ρ j)
  /-- no relator outside the block involves a generator of the block -/
  fox_outside : ∀ (i : α) (l : L), l ∉ Set.range g → @fox γ _ (f i) (τ l) = 0
  /-- the retraction restricts to the identity on the block -/
  retract_map : ∀ w : FreeGroup α, r (FreeGroup.map f w) = w
  /-- the retraction carries relators to relators -/
  retract_rel : ∀ l, r (τ l) ∈ relSub ρ

variable {ρ τ f g r} (hb : IsBlock ρ τ f g r)

include hb

theorem IsBlock.relSub_le_comap : relSub ρ ≤ (relSub τ).comap (FreeGroup.map f) := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨j, rfl⟩
  refine Subgroup.mem_comap.2 ?_
  rw [← hb.rel_eq j]
  exact Subgroup.subset_normalClosure (Set.mem_range_self _)

/-- The map of fundamental groups induced by the inclusion of the block. -/
def IsBlock.hom : PresGroup ρ →* PresGroup τ :=
  QuotientGroup.map _ _ (FreeGroup.map f) hb.relSub_le_comap

@[simp] theorem IsBlock.hom_mk (w : FreeGroup α) :
    hb.hom (QuotientGroup.mk w) = QuotientGroup.mk (FreeGroup.map f w) := rfl

theorem IsBlock.relSub_le_comap_retract : relSub τ ≤ (relSub ρ).comap r := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨l, rfl⟩
  exact Subgroup.mem_comap.2 (hb.retract_rel l)

/-- The retraction of the ambient presented group onto the block. -/
def IsBlock.retract : PresGroup τ →* PresGroup ρ :=
  QuotientGroup.map _ _ r hb.relSub_le_comap_retract

/-- **The block embeds**: its fundamental group is a faithful copy inside the big one. -/
theorem IsBlock.hom_injective : Function.Injective hb.hom := by
  refine Function.LeftInverse.injective (g := hb.retract) ?_
  intro x
  induction x using QuotientGroup.induction_on with
  | H w =>
      show hb.retract (QuotientGroup.mk (FreeGroup.map f w)) = _
      show (QuotientGroup.mk (r (FreeGroup.map f w)) : PresGroup ρ) = _
      rw [hb.retract_map]

/-- The ring map of group rings induced by the inclusion of the block. -/
noncomputable def IsBlock.ringHom :
    MonoidAlgebra ℤ (PresGroup ρ) →+* MonoidAlgebra ℤ (PresGroup τ) :=
  MonoidAlgebra.mapDomainRingHom ℤ hb.hom

theorem IsBlock.quot_freeRingMap (x : FreeGroupRing α) :
    quotRingHom ℤ (relSub τ) (freeRingMap f x) = hb.ringHom (quotRingHom ℤ (relSub ρ) x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single w m =>
      show quotRingHom ℤ (relSub τ)
          (MonoidAlgebra.mapDomain (FreeGroup.map f) (MonoidAlgebra.single w m)) = _
      rw [MonoidAlgebra.mapDomain_single, quotRingHom_single]
      show _ = MonoidAlgebra.mapDomain hb.hom (quotRingHom ℤ (relSub ρ) (MonoidAlgebra.single w m))
      rw [quotRingHom_single, MonoidAlgebra.mapDomain_single, IsBlock.hom_mk]

/-- The image of the block group inside the ambient group. -/
abbrev IsBlock.range : Subgroup (PresGroup τ) := hb.hom.range

/-- The group ring of the block, mapped onto the group ring of its image. -/
noncomputable def IsBlock.rangeRingHom :
    MonoidAlgebra ℤ (PresGroup ρ) →+* MonoidAlgebra ℤ hb.range :=
  MonoidAlgebra.mapDomainRingHom ℤ hb.hom.rangeRestrict

theorem IsBlock.subRingHom_rangeRingHom (y : MonoidAlgebra ℤ (PresGroup ρ)) :
    subRingHom hb.range (hb.rangeRingHom y) = hb.ringHom y := by
  show MonoidAlgebra.mapDomain (Subtype.val : hb.range → _)
      (MonoidAlgebra.mapDomain hb.hom.rangeRestrict y) = MonoidAlgebra.mapDomain hb.hom y
  rw [← MonoidAlgebra.mapDomain_comp]
  rfl

theorem IsBlock.rangeRingHom_surjective : Function.Surjective hb.rangeRingHom :=
  by
    intro y
    obtain ⟨x, hx⟩ := Finsupp.mapDomain_surjective hb.hom.rangeRestrict_surjective y.coeff
    exact ⟨MonoidAlgebra.ofCoeff x, MonoidAlgebra.coeff_injective hx⟩

theorem IsBlock.rangeRingHom_injective : Function.Injective hb.rangeRingHom := by
  have hr : Function.Injective hb.hom.rangeRestrict := fun a b hab => hb.hom_injective (congrArg Subtype.val hab)
  intro a b hab
  apply MonoidAlgebra.coeff_injective
  exact Finsupp.mapDomain_injective hr (congrArg MonoidAlgebra.coeff hab)

theorem IsBlock.augPres_ringHom (z : MonoidAlgebra ℤ (PresGroup ρ)) :
    augPres τ (hb.ringHom z) = augPres ρ z :=
  augQ_mapDomain hb.hom z

section FoxMatrix

variable [DecidableEq α]

/-- Inside the block the Fox matrix of `τ` is the image of the Fox matrix of `ρ`. -/
theorem IsBlock.foxMatrix_block (i : α) (j : J) :
    foxMatrixPres τ (f i) (g j) = hb.ringHom (foxMatrixPres ρ i j) := by
  have hfox : @fox γ _ (f i) (τ (g j)) = freeRingMap f (fox i (ρ j)) := by
    rw [hb.rel_eq j]
    exact fox_map f hb.gen_injective i (ρ j)
  show quotRingHom ℤ (relSub τ) (fox (f i) (τ (g j))) = _
  rw [hfox, hb.quot_freeRingMap]
  rfl

variable [Fintype J] [Fintype L]

/-- **The block coordinates of a Fox cycle have zero augmentation** when the block is
Cockcroft.  This is the statement "the factor retractions detect every coordinate of a
Hurewicz image" of Lemma 3.10. -/
theorem augPres_block_eq_zero (hρ : IsCockcroft ρ)
    {v : L → MonoidAlgebra ℤ (PresGroup τ)} (hv : IsFoxCycle τ v) (j : J) :
    augPres τ (v (g j)) = 0 := by
  classical
  set H := hb.range with hH
  set A : α → J → MonoidAlgebra ℤ H := fun i j => hb.rangeRingHom (foxMatrixPres ρ i j) with hA
  -- the block coordinates form a cycle of the Fox matrix of the block
  have hcyc : ∀ i : α, ∑ j : J, v (g j) * subRingHom H (A i j) = 0 := by
    intro i
    have h := hv (f i)
    have hrestrict : ∑ l : L, v l * foxMatrixPres τ (f i) l
        = ∑ j : J, v (g j) * foxMatrixPres τ (f i) (g j) := by
      rw [← Finset.sum_image (f := fun l => v l * foxMatrixPres τ (f i) l)
        (g := g) (s := Finset.univ) (by intro a _ b _ hab; exact hb.cell_injective hab)]
      refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro l _ hl
      have : l ∉ Set.range g := by
        intro ⟨j, hj⟩
        exact hl (Finset.mem_image.2 ⟨j, Finset.mem_univ j, hj⟩)
      have hz : foxMatrixPres τ (f i) l = 0 := by
        show quotRingHom ℤ (relSub τ) (fox (f i) (τ l)) = 0
        rw [hb.fox_outside i l this, map_zero]
      rw [hz, mul_zero]
    rw [hrestrict] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => by
      rw [hA, hb.subRingHom_rangeRingHom, hb.foxMatrix_block]
  have hspan := cycle_mem_span_subgroup_cycles H A (fun j => v (g j)) hcyc
  -- the augmentation vanishes on the spanning set, hence on the whole span
  set N : Submodule (MonoidAlgebra ℤ (PresGroup τ)) (J → MonoidAlgebra ℤ (PresGroup τ)) :=
    { carrier := {w | ∀ j, augPres τ (w j) = 0}
      add_mem' := by
        intro a b ha hb' j
        rw [Pi.add_apply, map_add, ha j, hb' j, add_zero]
      zero_mem' := by
        intro j
        simp
      smul_mem' := by
        intro c a ha j
        rw [Pi.smul_apply, smul_eq_mul, map_mul, ha j, mul_zero] } with hN
  have hgen : subgroupCycles H A ⊆ (N : Set (J → MonoidAlgebra ℤ (PresGroup τ))) := by
    rintro _ ⟨y', hy', rfl⟩ j
    choose y hy using fun j => hb.rangeRingHom_surjective (y' j)
    have hcycy : IsFoxCycle ρ y := by
      intro i
      refine hb.rangeRingHom_injective ?_
      rw [map_sum, map_zero, ← hy' i]
      exact Finset.sum_congr rfl fun j _ => by rw [map_mul, hy j]
    show augPres τ (subRingHom H (y' j)) = 0
    rw [← hy j, hb.subRingHom_rangeRingHom, hb.augPres_ringHom]
    exact hρ y hcycy j
  exact Submodule.span_le.2 hgen hspan (j := j)

end FoxMatrix

end FiniteChains
