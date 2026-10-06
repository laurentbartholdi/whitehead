module

public import RequestProject.FreeGeneratorPaddingFinsupp

@[expose] public section

/-! Literal labelled presentation inclusions as actual supported structural
maps. The boundary proof includes both generator and cell index changes.
Awaiting final Lean verification.
-/

noncomputable section
open scoped Classical

namespace FiniteChains.PresInclusionFS
open BlockFamily

variable {A B J K : Type} (ρ : J → FreeGroup A) (τ : K → FreeGroup B)
  (g : A → B) (f : J → K) (hg : Function.Injective g) (hf : Function.Injective f)
  (hrel : ∀ j, τ (f j) = FreeGroup.map g (ρ j))

def groupHom : PresGroup ρ →* PresGroup τ :=
  QuotientGroup.map _ _ (FreeGroup.map g) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    apply Subgroup.mem_comap.mpr
    rw [← hrel j]
    exact Subgroup.subset_normalClosure ⟨f j, rfl⟩)

def coefficients := MonoidAlgebra.mapDomainRingHom ℤ (groupHom ρ τ g f hrel)

theorem coefficients_proj (x : FreeGroupRing A) :
    coefficients ρ τ g f hrel (proj (relSub ρ) x) =
      proj (relSub τ) (freeRingMap g x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp [coefficients]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single w a =>
      apply MonoidAlgebra.coeff_injective
      change Finsupp.mapDomain (groupHom ρ τ g f hrel)
        (Finsupp.mapDomain (QuotientGroup.mk' (relSub ρ)) (Finsupp.single w a)) =
        Finsupp.mapDomain (QuotientGroup.mk' (relSub τ))
          (Finsupp.mapDomain (FreeGroup.map g) (Finsupp.single w a))
      simp only [Finsupp.mapDomain_single]
      rfl

variable [DecidableEq A] [DecidableEq B]

include hg in
theorem gradient (j : J) :
    coverFoxGradient (relSub τ) (τ (f j)) =
      Finsupp.mapDomain g ((coverFoxGradient (relSub ρ) (ρ j)).mapRange
        (coefficients ρ τ g f hrel) (map_zero _)) := by
  ext b : 1
  rw [hrel j]
  by_cases hb : b ∈ Set.range g
  · obtain ⟨a, rfl⟩ := hb
    rw [Finsupp.mapDomain_apply_of_injective hg]
    change proj _ (fox (g a) (FreeGroup.map g (ρ j))) =
      coefficients ρ τ g f hrel (proj _ (fox a (ρ j)))
    rw [fox_map g hg, coefficients_proj]
  · rw [Finsupp.mapDomain_notin_range _ b hb]
    change proj _ (fox b (FreeGroup.map g (ρ j))) = 0
    rw [fox_map_of_not_mem_range g (fun a h => hb ⟨a, h.symm⟩), map_zero]

def cells (x : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    K →₀ MonoidAlgebra ℤ (PresGroup τ) :=
  Finsupp.mapDomain f (x.mapRange (coefficients ρ τ g f hrel) (map_zero _))

omit [DecidableEq A] [DecidableEq B] in
@[simp] theorem cells_single (j : J) (a : MonoidAlgebra ℤ (PresGroup ρ)) :
    cells ρ τ g f hrel (Finsupp.single j a) =
      Finsupp.single (f j) (coefficients ρ τ g f hrel a) := by
  simp [cells]

include hg in
theorem boundary (x : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    coverSecondBoundary (relSub τ) τ (cells ρ τ g f hrel x) =
      Finsupp.mapDomain g ((coverSecondBoundary (relSub ρ) ρ x).mapRange
        (coefficients ρ τ g f hrel) (map_zero _)) := by
  induction x using Finsupp.induction_linear with
  | zero => simp [cells]
  | add x y hx hy =>
      simp only [cells, Finsupp.mapRange_add', Finsupp.mapDomain_add, map_add] at *
      rw [hx, hy]
  | single j a =>
      rw [cells_single, coverSecondBoundary_single, coverSecondBoundary_single,
        gradient ρ τ g f hg hrel j]
      have hmap : (a • coverFoxGradient (relSub ρ) (ρ j)).mapRange
          (coefficients ρ τ g f hrel) (map_zero _) =
        coefficients ρ τ g f hrel a •
          (coverFoxGradient (relSub ρ) (ρ j)).mapRange
            (coefficients ρ τ g f hrel) (map_zero _) := by
        ext i : 1
        simp only [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul]
        exact map_mul _ _ _
      rw [hmap, Finsupp.mapDomain_smul]

def mor : PresMorFS ρ τ where
  hom := groupHom ρ τ g f hrel
  cells := cells ρ τ g f hrel
  cells_add := by intro x y; simp [cells, Finsupp.mapRange_add', Finsupp.mapDomain_add]
  cells_smul := by
    intro a x
    have h : (a • x).mapRange (coefficients ρ τ g f hrel) (map_zero _) =
        coefficients ρ τ g f hrel a • x.mapRange (coefficients ρ τ g f hrel) (map_zero _) := by
      ext j : 1
      simp only [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul]
      exact map_mul _ _ _
    change Finsupp.mapDomain f _ = _
    rw [h, Finsupp.mapDomain_smul]
    rfl
  cells_cycle := by
    intro x hx
    change coverSecondBoundary _ _ _ = 0
    rw [boundary ρ τ g f hg hrel, hx]
    simp
  cells_aug := by
    intro x hx k
    by_cases hk : k ∈ Set.range f
    · obtain ⟨j, rfl⟩ := hk
      change augPres τ (Finsupp.mapDomain f _ (f j)) = 0
      rw [Finsupp.mapDomain_apply_of_injective hf]
      change augPres τ (MonoidAlgebra.mapDomainRingHom ℤ (groupHom ρ τ g f hrel) (x j)) = 0
      exact (augQ_mapDomain (groupHom ρ τ g f hrel) (x j)).trans (hx j)
    · change augPres τ (Finsupp.mapDomain f _ k) = 0
      rw [Finsupp.mapDomain_notin_range _ k hk, map_zero]

end FiniteChains.PresInclusionFS
