module

public import RequestProject.RelativeStructuralOperation
public import RequestProject.FoxNaturality

@[expose] public section

/-! Padding a presentation by any set of free generators preserves the
generation equation, including for infinite cell sets. This lets all
positive stages share one ambient alphabet and supplies a fresh terminal
cap when the original extra alphabet was empty. Unverified source.
-/

noncomputable section
open scoped Classical

namespace FiniteChains
open BlockFamily

namespace FreePadding
variable {A B J : Type} (ρ : J → FreeGroup A) (f : A → B) (hf : Function.Injective f)

def rel : J → FreeGroup B := fun j => FreeGroup.map f (ρ j)

def groupHom : PresGroup ρ →* PresGroup (rel ρ f) :=
  QuotientGroup.map _ _ (FreeGroup.map f) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    exact Subgroup.subset_normalClosure ⟨j, rfl⟩)

def wordRetraction : FreeGroup B →* FreeGroup A :=
  FreeGroup.lift (fun b => if h : ∃ a, f a = b then FreeGroup.of h.choose else 1)

include hf in
theorem wordRetraction_map (w : FreeGroup A) :
    wordRetraction f (FreeGroup.map f w) = w := by
  have hmap : (wordRetraction f).comp (FreeGroup.map f) = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro a
    have he : ∃ a', f a' = f a := ⟨a, rfl⟩
    simp only [MonoidHom.comp_apply, FreeGroup.map.of, wordRetraction,
      FreeGroup.lift_apply_of, dif_pos he, MonoidHom.id_apply]
    exact congrArg FreeGroup.of (hf he.choose_spec)
  exact congrArg (fun h : FreeGroup A →* FreeGroup A => h w) hmap

def groupRetraction : PresGroup (rel ρ f) →* PresGroup ρ :=
  QuotientGroup.lift _ ((QuotientGroup.mk' _).comp (wordRetraction f)) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    change QuotientGroup.mk (wordRetraction f (FreeGroup.map f (ρ j))) = 1
    rw [wordRetraction_map f hf]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨j, rfl⟩))

include hf in
theorem groupHom_injective : Function.Injective (groupHom ρ f) := by
  apply Function.LeftInverse.injective (g := groupRetraction ρ f hf)
  intro g
  induction g using QuotientGroup.induction_on with
  | H w =>
      change QuotientGroup.mk (wordRetraction f (FreeGroup.map f w)) = QuotientGroup.mk w
      rw [wordRetraction_map f hf]

def coefficients := MonoidAlgebra.mapDomainRingHom ℤ (groupHom ρ f)

theorem coefficients_proj (x : FreeGroupRing A) :
    coefficients ρ f (proj (relSub ρ) x) =
      proj (relSub (rel ρ f)) (freeRingMap f x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp [coefficients]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single w a =>
      apply MonoidAlgebra.coeff_injective
      change Finsupp.mapDomain (groupHom ρ f)
        (Finsupp.mapDomain (QuotientGroup.mk' (relSub ρ)) (Finsupp.single w a)) =
        Finsupp.mapDomain (QuotientGroup.mk' (relSub (rel ρ f)))
          (Finsupp.mapDomain (FreeGroup.map f) (Finsupp.single w a))
      simp only [Finsupp.mapDomain_single]
      rfl

variable [DecidableEq A] [DecidableEq B]

include hf in
theorem matrix_retained (a : A) (j : J) :
    foxMatrixPres (rel ρ f) (f a) j = coefficients ρ f (foxMatrixPres ρ a j) := by
  change proj _ (fox (f a) (FreeGroup.map f (ρ j))) = _
  rw [fox_map f hf, ← coefficients_proj]
  rfl

omit [DecidableEq A] in
theorem matrix_fresh (b : B) (hb : b ∉ Set.range f) (j : J) :
    foxMatrixPres (rel ρ f) b j = 0 := by
  change proj _ (fox b (FreeGroup.map f (ρ j))) = 0
  rw [fox_map_of_not_mem_range f (fun a h => hb ⟨a, h.symm⟩), map_zero]

def oldBoundary := fsRingMapBoundary (coefficients ρ f)
  (fun j => coverFoxGradient (relSub ρ) (ρ j))

include hf in
theorem boundary_retained
    (x : J →₀ MonoidAlgebra ℤ (PresGroup (rel ρ f))) (a : A) :
    coverSecondBoundary (relSub (rel ρ f)) (rel ρ f) x (f a) = oldBoundary ρ f x a := by
  rw [fsCoverSecondBoundary_apply]
  simp only [oldBoundary, fsRingMapBoundary, Finsupp.linearCombination_apply,
    Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.mapRange_apply]
  apply Finsupp.sum_congr
  intro j hj
  rw [matrix_retained ρ f hf]
  rfl

def structuralMap : PresMorFS ρ (rel ρ f) where
  hom := groupHom ρ f
  cells := fun x => x.mapRange (coefficients ρ f) (map_zero _)
  cells_add := by
    intro x y
    ext j : 1
    simp only [Finsupp.mapRange_apply, Finsupp.add_apply]
    exact map_add _ _ _
  cells_smul := by
    intro a x
    ext j : 1
    simp only [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul]
    exact map_mul _ _ _
  cells_cycle := by
    intro x hx
    change coverSecondBoundary _ _ _ = 0
    ext b : 1
    by_cases hb : b ∈ Set.range f
    · obtain ⟨a, rfl⟩ := hb
      rw [boundary_retained ρ f hf]
      change fsRingMapBoundary (coefficients ρ f) _ (x.mapRange _ _) a = 0
      rw [fsRingMapBoundary_mapRange]
      erw [hx]
      rfl
    · rw [fsCoverSecondBoundary_apply]
      rw [Finsupp.sum]
      apply Finset.sum_eq_zero
      intro j hj
      rw [matrix_fresh ρ f b hb, mul_zero]
  cells_aug := by
    intro x hx j
    change augPres (rel ρ f) (MonoidAlgebra.mapDomainRingHom ℤ (groupHom ρ f) (x j)) = 0
    exact (augQ_mapDomain (groupHom ρ f) (x j)).trans (hx j)

theorem structuralMap_generates : FSGenerates (structuralMap ρ f hf) := by
  intro x hx
  have hz : oldBoundary ρ f x = 0 := by
    ext a : 1
    rw [← boundary_retained ρ f hf, hx]
    rfl
  exact fs_cycle_mem_span_groupMap_cycles (groupHom ρ f) (groupHom_injective ρ f hf)
    (fun j => coverFoxGradient (relSub ρ) (ρ j)) x hz

end FreePadding
end FiniteChains
