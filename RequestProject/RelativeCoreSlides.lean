module

public import RequestProject.RelativeNormalizedRestrictions
public import RequestProject.SimultaneousCoreSlidesFinsupp

@[expose] public section

/-! Actual finite-support simultaneous rule 2. The correction chains are
chosen in the core-only presentation, before any extra relators are imposed.
Consequently all later stage maps use the same core chain choices.

-/

noncomputable section
open scoped Classical

namespace FiniteChains.RelativeNormalForm
open Davis Davis.Genus BlockFamily

variable {A C Z S : Type} (core : C → FreeGroup A)
  (hcore : Function.Surjective (expMatrix core))

def pairCorePresentation : C → FreeGroup (PairGen A Z) :=
  fun c => FreeGroup.map Sum.inl (core c)

def pairCorrection (w : FreeGroup (A ⊕ Z)) : FreeGroup (PairGen A Z) :=
  FreeGroup.map Sum.inl (correctionWord core (correctionCoefficients core hcore w))

theorem pairCorrection_mem (w : FreeGroup (A ⊕ Z)) :
    pairCorrection core hcore w ∈ relSub (pairCorePresentation (Z := Z) core) :=
  coreCorrection_mem core (relSub (pairCorePresentation (Z := Z) core))
    (fun c => Subgroup.subset_normalClosure ⟨c, rfl⟩) _

theorem pairCorrection_filling_exists (w : FreeGroup (A ⊕ Z)) :
    ∃ v : C →₀ MonoidAlgebra ℤ (PresGroup (pairCorePresentation (Z := Z) core)),
      coverSecondBoundary (relSub (pairCorePresentation (Z := Z) core))
        (pairCorePresentation core) v =
      coverFoxGradient (relSub (pairCorePresentation (Z := Z) core))
        (pairCorrection core hcore w) := by
  apply (coverFoxGradient_mem_range_iff (relSub (pairCorePresentation (Z := Z) core))
    (pairCorePresentation (Z := Z) core)
    (fun c => Subgroup.subset_normalClosure ⟨c, rfl⟩)
    (pairCorrection_mem core hcore w)).mpr
  exact (le_sup_left : relSub (pairCorePresentation (Z := Z) core) ≤
    relSub (pairCorePresentation (Z := Z) core) ⊔
      ⁅relSub (pairCorePresentation (Z := Z) core),
        relSub (pairCorePresentation (Z := Z) core)⁆) (pairCorrection_mem core hcore w)

def pairCorrectionFilling (w : FreeGroup (A ⊕ Z)) :
    C →₀ MonoidAlgebra ℤ (PresGroup (pairCorePresentation (Z := Z) core)) :=
  Classical.choose (pairCorrection_filling_exists core hcore w)

theorem pairCorrectionFilling_boundary (w : FreeGroup (A ⊕ Z)) :
    coverSecondBoundary (relSub (pairCorePresentation (Z := Z) core))
      (pairCorePresentation core) (pairCorrectionFilling core hcore w) =
    coverFoxGradient (relSub (pairCorePresentation (Z := Z) core))
      (pairCorrection core hcore w) :=
  Classical.choose_spec (pairCorrection_filling_exists core hcore w)

variable (extra : S → FreeGroup (A ⊕ Z))

def slideGroupHom : PresGroup (beforeCorrection core extra) →*
    PresGroup (normalizedPresentation core hcore extra) :=
  QuotientGroup.map _ _ (MonoidHom.id _) (by
    rw [Subgroup.comap_id, relSub_normalizedPresentation core hcore extra])

def slideGroupInverse : PresGroup (normalizedPresentation core hcore extra) →*
    PresGroup (beforeCorrection core extra) :=
  QuotientGroup.map _ _ (MonoidHom.id _) (by
    rw [Subgroup.comap_id, relSub_normalizedPresentation core hcore extra])

theorem slideGroupHom_injective :
    Function.Injective (slideGroupHom core hcore extra) := by
  apply Function.LeftInverse.injective (g := slideGroupInverse core hcore extra)
  intro g
  induction g using QuotientGroup.induction_on with
  | H w => rfl

def pairCoreToNormalized : PresGroup (pairCorePresentation (Z := Z) core) →*
    PresGroup (normalizedPresentation core hcore extra) :=
  QuotientGroup.map _ _ (MonoidHom.id _) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨c, rfl⟩
    exact Subgroup.subset_normalClosure ⟨Sum.inl c, rfl⟩)

theorem ringMap_quotient_word {G H : Subgroup (FreeGroup (PairGen A Z))}
    [G.Normal] [H.Normal] (f : (FreeGroup (PairGen A Z) ⧸ G) →*
      (FreeGroup (PairGen A Z) ⧸ H))
    (hf : ∀ w, f (QuotientGroup.mk w) = QuotientGroup.mk w)
    (x : FreeGroupRing (PairGen A Z)) :
    MonoidAlgebra.mapDomainRingHom ℤ f (proj G x) = proj H x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  | single w a =>
      apply MonoidAlgebra.coeff_injective
      change Finsupp.mapDomain f (Finsupp.mapDomain (QuotientGroup.mk' G)
        (Finsupp.single w a)) = Finsupp.mapDomain (QuotientGroup.mk' H) (Finsupp.single w a)
      simp only [Finsupp.mapDomain_single, QuotientGroup.mk'_apply, hf]

theorem gradient_groupMap {G H : Subgroup (FreeGroup (PairGen A Z))}
    [G.Normal] [H.Normal] (f : (FreeGroup (PairGen A Z) ⧸ G) →*
      (FreeGroup (PairGen A Z) ⧸ H))
    (hf : ∀ w, f (QuotientGroup.mk w) = QuotientGroup.mk w)
    (w : FreeGroup (PairGen A Z)) :
    (coverFoxGradient G w).mapRange (MonoidAlgebra.mapDomainRingHom ℤ f) (map_zero _) =
      coverFoxGradient H w := by
  ext i : 1
  exact ringMap_quotient_word f hf (fox i w)

def slideCoefficients := MonoidAlgebra.mapDomainRingHom ℤ (slideGroupHom core hcore extra)

def slideCoreCoefficients :=
  MonoidAlgebra.mapDomainRingHom ℤ (pairCoreToNormalized core hcore extra)

/-- Actual correction columns in the target ring, obtained from fixed
core-only chains. There is no dependence of the choice on the stage group. -/
def slideColumns (s : S) :
    C →₀ MonoidAlgebra ℤ (PresGroup (normalizedPresentation core hcore extra)) :=
  (pairCorrectionFilling core hcore (extra s)).mapRange
    (slideCoreCoefficients core hcore extra) (map_zero _)

def slideOldBoundary :
    ((C ⊕ S) →₀ MonoidAlgebra ℤ (PresGroup (normalizedPresentation core hcore extra))) →ₗ[
      MonoidAlgebra ℤ (PresGroup (normalizedPresentation core hcore extra))]
      (PairGen A Z →₀ MonoidAlgebra ℤ (PresGroup (normalizedPresentation core hcore extra))) :=
  fsRingMapBoundary (slideCoefficients core hcore extra)
    (fun j => coverFoxGradient (relSub (beforeCorrection core extra))
      (beforeCorrection core extra j))

theorem slideOldBoundary_single (k : C ⊕ S)
    (a : MonoidAlgebra ℤ (PresGroup (normalizedPresentation core hcore extra))) :
    slideOldBoundary core hcore extra (Finsupp.single k a) =
      a • coverFoxGradient (relSub (normalizedPresentation core hcore extra))
        (beforeCorrection core extra k) := by
  rw [slideOldBoundary, fsRingMapBoundary, Finsupp.linearCombination_single]
  congr 1
  exact gradient_groupMap (slideGroupHom core hcore extra) (fun _ => rfl) _

theorem slideColumns_boundary (s : S) :
    slideOldBoundary core hcore extra (fsOldOneIncl (slideColumns core hcore extra s)) =
      coverFoxGradient (relSub (normalizedPresentation core hcore extra))
        (pairCorrection core hcore (extra s)) := by
  have hm : (slideOldBoundary core hcore extra).comp fsOldOneIncl =
      fsRingMapBoundary (slideCoreCoefficients core hcore extra)
        (fun c => coverFoxGradient (relSub (pairCorePresentation (Z := Z) core))
          (pairCorePresentation core c)) := by
    apply Finsupp.lhom_ext
    intro c a
    simp only [LinearMap.comp_apply, fsOldOneIncl_single, slideOldBoundary_single,
      fsRingMapBoundary, Finsupp.linearCombination_single]
    congr 1
    exact (gradient_groupMap (pairCoreToNormalized core hcore extra) (fun _ => rfl) _).symm
  change ((slideOldBoundary core hcore extra).comp fsOldOneIncl)
    ((pairCorrectionFilling core hcore (extra s)).mapRange
      (slideCoreCoefficients core hcore extra) (map_zero _)) = _
  rw [hm, fsRingMapBoundary_mapRange]
  erw [pairCorrectionFilling_boundary]
  exact gradient_groupMap (pairCoreToNormalized core hcore extra) (fun _ => rfl) _

/-- The actual normalized Fox boundary is the old boundary after the
explicit triangular correction. -/
theorem normalizationSlide_boundary
    (x : (C ⊕ S) →₀ MonoidAlgebra ℤ (PresGroup (normalizedPresentation core hcore extra))) :
    coverSecondBoundary (relSub (normalizedPresentation core hcore extra))
      (normalizedPresentation core hcore extra) x =
    slideOldBoundary core hcore extra (coreSlideReverse (slideColumns core hcore extra) x) := by
  apply coreSlide_boundary (slideColumns core hcore extra)
    (slideOldBoundary core hcore extra) _ ?_ ?_ x
  · intro c
    rw [coverSecondBoundary_single, slideOldBoundary_single]
    rfl
  · intro s
    rw [coverSecondBoundary_single, one_smul, slideOldBoundary_single, one_smul,
      slideColumns_boundary]
    change coverFoxGradient _ (normalizedWord core hcore (extra s)) = _
    rw [normalizedWord_eq]
    exact coverFoxGradient_mul _ (by
      rw [relSub_normalizedPresentation]
      exact Subgroup.subset_normalClosure ⟨Sum.inr s, rfl⟩) _

def normalizationSlideMap : PresMorFS (beforeCorrection core extra)
    (normalizedPresentation core hcore extra) where
  hom := slideGroupHom core hcore extra
  cells := fun x => coreSlideForward (slideColumns core hcore extra)
    (x.mapRange (slideCoefficients core hcore extra) (map_zero _))
  cells_add := by
    intro x y
    rw [Finsupp.mapRange_add, map_add]
    exact map_add _
  cells_smul := by
    intro a x
    have h : (a • x).mapRange (slideCoefficients core hcore extra) (map_zero _) =
        (slideCoefficients core hcore extra a) •
          x.mapRange (slideCoefficients core hcore extra) (map_zero _) := by
      ext k : 1
      simp only [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul]
      exact map_mul _ _ _
    rw [h, map_smul]
    rfl
  cells_cycle := by
    intro x hx
    change coverSecondBoundary _ _ _ = 0
    rw [normalizationSlide_boundary, coreSlideReverse_forward]
    change fsRingMapBoundary (slideCoefficients core hcore extra) _
      (x.mapRange _ _) = 0
    rw [fsRingMapBoundary_mapRange]
    erw [hx]
    simp
  cells_aug := by
    intro x hx k
    apply coreSlideForward_aug_zero
    intro j
    change augPres (normalizedPresentation core hcore extra)
      (MonoidAlgebra.mapDomainRingHom ℤ (slideGroupHom core hcore extra) (x j)) = 0
    exact (augQ_mapDomain (slideGroupHom core hcore extra) (x j)).trans (hx j)

/-- Genuine rule-2 generation for arbitrary cores and relator families.
All correction columns and all boundary equations are constructed above. -/
theorem normalizationSlideMap_generates :
    FSGenerates (normalizationSlideMap core hcore extra) := by
  intro x hx
  let y := coreSlideReverse (slideColumns core hcore extra) x
  have hy : slideOldBoundary core hcore extra y = 0 :=
    (normalizationSlide_boundary core hcore extra x).symm.trans hx
  have hspan := fs_cycle_mem_span_groupMap_cycles (slideGroupHom core hcore extra)
    (slideGroupHom_injective core hcore extra)
    (fun j => coverFoxGradient (relSub (beforeCorrection core extra))
      (beforeCorrection core extra j)) y hy
  have he : coreSlideForward (slideColumns core hcore extra) y = x :=
    coreSlideForward_reverse _ _
  rw [← he]
  clear hx hy he
  generalize y = z at hspan ⊢
  clear y x
  induction hspan using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a, ha, rfl⟩ := hz
      exact Submodule.subset_span ⟨a, ha, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add z w _ _ hz hw => rw [map_add]; exact Submodule.add_mem _ hz hw
  | smul a z _ hz => rw [map_smul]; exact Submodule.smul_mem _ a hz

/-- Rules 2 and 3, in their actual arbitrary-family finite-support form. -/
def normalizedBlockMap : PresMorFS (beforeCorrection core extra)
    (blockPresentation core hcore extra) :=
  (blockStructuralMap core hcore extra).comp (normalizationSlideMap core hcore extra)

theorem normalizedBlockMap_generates : FSGenerates (normalizedBlockMap core hcore extra) :=
  (blockStructuralMap_generates core hcore extra).comp
    (normalizationSlideMap_generates core hcore extra)

end FiniteChains.RelativeNormalForm
