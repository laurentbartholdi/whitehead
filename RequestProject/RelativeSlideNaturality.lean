module

public import RequestProject.RelativeRuleOneNaturality
public import RequestProject.RelativeCoreSlides

@[expose] public section

/-! Simultaneous core slides respect all restrictions of the shared ambient
relator labels. This completes actual zero-arrow preservation for rules
1, 2 and 3, with no commuting-square hypothesis. Unverified source.
-/

noncomputable section
open scoped Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.RelativeNormalForm
open BlockFamily

variable {A C Z S : Type} (core : C → FreeGroup A)
  (hcore : Function.Surjective (expMatrix core))
  (extra : S → FreeGroup (A ⊕ Z))
  {p t : S → Prop} (hpt : ∀ s, p s → t s)

theorem slide_group_square :
    (normalizedInclusion core hcore extra hpt).hom.comp
      (slideGroupHom core hcore (restrictedExtra extra p)) =
    (slideGroupHom core hcore (restrictedExtra extra t)).comp
      (pairInclusion core extra hpt).hom := by
  apply MonoidHom.ext
  intro g
  induction g using QuotientGroup.induction_on with
  | H w =>
      change (QuotientGroup.mk (FreeGroup.map id w) :
        PresGroup (restrictedPresentation core hcore extra t)) =
          QuotientGroup.mk (FreeGroup.map id w)
      rfl

theorem slide_core_group_square :
    (normalizedInclusion core hcore extra hpt).hom.comp
      (pairCoreToNormalized core hcore (restrictedExtra extra p)) =
    pairCoreToNormalized core hcore (restrictedExtra extra t) := by
  apply MonoidHom.ext
  intro g
  induction g using QuotientGroup.induction_on with
  | H w =>
      change QuotientGroup.mk (FreeGroup.map id w) = QuotientGroup.mk w
      simp

theorem slide_columns_natural (s : {s // p s}) :
    (slideColumns core hcore (restrictedExtra extra p) s).mapRange
      (MonoidAlgebra.mapDomainRingHom ℤ (normalizedInclusion core hcore extra hpt).hom)
      (map_zero _) =
    slideColumns core hcore (restrictedExtra extra t) (labelIncl hpt s) := by
  ext c : 1
  change MonoidAlgebra.mapDomainRingHom ℤ (normalizedInclusion core hcore extra hpt).hom
    (MonoidAlgebra.mapDomainRingHom ℤ (pairCoreToNormalized core hcore (restrictedExtra extra p))
      (pairCorrectionFilling core hcore (extra s.val) c)) = _
  erw [BlockMor.mapDomainRingHom_comp']
  erw [slide_core_group_square]
  rfl

theorem normalizedInclusion_core_chain
    (x : C →₀ MonoidAlgebra ℤ (PresGroup (restrictedPresentation core hcore extra p))) :
    (normalizedInclusion core hcore extra hpt).cells (fsOldOneIncl x) =
      fsOldOneIncl (x.mapRange (MonoidAlgebra.mapDomainRingHom ℤ
        (normalizedInclusion core hcore extra hpt).hom) (map_zero _)) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, PresMorFS.cells_add, hx, hy, Finsupp.mapRange_add', map_add]
  | single c a =>
      rw [fsOldOneIncl_single, Finsupp.mapRange_single, fsOldOneIncl_single]
      change Finsupp.mapDomain (oldCellIncl hpt)
        ((Finsupp.single (Sum.inl c) a).mapRange _ _) = _
      rw [Finsupp.mapRange_single, Finsupp.mapDomain_single]
      rfl

theorem slide_correction_natural
    (x : (C ⊕ {s // p s}) →₀ MonoidAlgebra ℤ
      (PresGroup (restrictedPresentation core hcore extra p))) :
    (normalizedInclusion core hcore extra hpt).cells
      (coreSlideCorrection (slideColumns core hcore (restrictedExtra extra p)) x) =
    coreSlideCorrection (slideColumns core hcore (restrictedExtra extra t))
      ((normalizedInclusion core hcore extra hpt).cells x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, PresMorFS.cells_add, PresMorFS.cells_add, map_add, hx, hy]
  | single k a =>
      have hi : (normalizedInclusion core hcore extra hpt).cells (Finsupp.single k a) =
          Finsupp.single (oldCellIncl hpt k)
            (MonoidAlgebra.mapDomainRingHom ℤ (normalizedInclusion core hcore extra hpt).hom a) := by
        change Finsupp.mapDomain _ ((Finsupp.single k a).mapRange _ _) = _
        rw [Finsupp.mapRange_single, Finsupp.mapDomain_single]
        rfl
      rw [hi]
      cases k with
      | inl c => simp [oldCellIncl]
      | inr s =>
          rw [coreSlideCorrection_single_inr, PresMorFS.cells_smul]
          change _ = coreSlideCorrection _ (Finsupp.single (Sum.inr (labelIncl hpt s)) _)
          rw [coreSlideCorrection_single_inr]
          exact congrArg (fun z => MonoidAlgebra.mapDomainRingHom ℤ
              (normalizedInclusion core hcore extra hpt).hom a • z)
            ((normalizedInclusion_core_chain core hcore extra hpt
                (slideColumns core hcore (restrictedExtra extra p) s)).trans
              (congrArg (fsOldOneIncl (Z := {s // t s}))
                (slide_columns_natural core hcore extra hpt s)))

theorem slide_forward_natural
    (x : (C ⊕ {s // p s}) →₀ MonoidAlgebra ℤ
      (PresGroup (restrictedPresentation core hcore extra p))) :
    (normalizedInclusion core hcore extra hpt).cells
      (coreSlideForward (slideColumns core hcore (restrictedExtra extra p)) x) =
    coreSlideForward (slideColumns core hcore (restrictedExtra extra t))
      ((normalizedInclusion core hcore extra hpt).cells x) := by
  change (normalizedInclusion core hcore extra hpt).cells (x - _) = _ - _
  rw [PresMorFS.cells_sub, slide_correction_natural]
  rfl

theorem slide_coefficient_chain_square
    (x : (C ⊕ {s // p s}) →₀ MonoidAlgebra ℤ
      (PresGroup (beforeCorrection core (restrictedExtra extra p)))) :
    (normalizedInclusion core hcore extra hpt).cells
      (x.mapRange (slideCoefficients core hcore (restrictedExtra extra p)) (map_zero _)) =
    ((pairInclusion core extra hpt).cells x).mapRange
      (slideCoefficients core hcore (restrictedExtra extra t)) (map_zero _) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      have hp := Finsupp.mapRange_add'
        (f := slideCoefficients core hcore (restrictedExtra extra p)) x y
      have ht := Finsupp.mapRange_add'
        (f := slideCoefficients core hcore (restrictedExtra extra t))
        ((pairInclusion core extra hpt).cells x) ((pairInclusion core extra hpt).cells y)
      rw [hp, PresMorFS.cells_add, PresMorFS.cells_add, ht, hx, hy]
  | single j a =>
      rw [Finsupp.mapRange_single]
      change Finsupp.mapDomain (oldCellIncl hpt) ((Finsupp.single j _).mapRange _ _) =
        (Finsupp.mapDomain (oldCellIncl hpt) ((Finsupp.single j a).mapRange _ _)).mapRange _ _
      rw [Finsupp.mapRange_single, Finsupp.mapDomain_single,
        Finsupp.mapRange_single, Finsupp.mapDomain_single, Finsupp.mapRange_single]
      congr 1
      change MonoidAlgebra.mapDomainRingHom ℤ (normalizedInclusion core hcore extra hpt).hom
          (MonoidAlgebra.mapDomainRingHom ℤ
            (slideGroupHom core hcore (restrictedExtra extra p)) a) =
        MonoidAlgebra.mapDomainRingHom ℤ (slideGroupHom core hcore (restrictedExtra extra t))
          (MonoidAlgebra.mapDomainRingHom ℤ (pairInclusion core extra hpt).hom a)
      erw [BlockMor.mapDomainRingHom_comp', BlockMor.mapDomainRingHom_comp', slide_group_square]
      rfl

theorem slide_chain_square
    (x : (C ⊕ {s // p s}) →₀ MonoidAlgebra ℤ
      (PresGroup (beforeCorrection core (restrictedExtra extra p)))) :
    (normalizedInclusion core hcore extra hpt).cells
      ((normalizationSlideMap core hcore (restrictedExtra extra p)).cells x) =
    (normalizationSlideMap core hcore (restrictedExtra extra t)).cells
      ((pairInclusion core extra hpt).cells x) := by
  change (normalizedInclusion core hcore extra hpt).cells (coreSlideForward _ _) =
    coreSlideForward _ _
  exact (slide_forward_natural core hcore extra hpt
    (x.mapRange (slideCoefficients core hcore (restrictedExtra extra p)) (map_zero _))).trans
      (congrArg (coreSlideForward (slideColumns core hcore (restrictedExtra extra t)))
        (slide_coefficient_chain_square core hcore extra hpt x))

theorem slide_preserves_zero
    (hzero : ∀ x, FSIsFoxCycle (beforeCorrection core (restrictedExtra extra p)) x →
      (pairInclusion core extra hpt).cells x = 0)
    {x} (hx : FSIsFoxCycle (restrictedPresentation core hcore extra p) x) :
    (normalizedInclusion core hcore extra hpt).cells x = 0 :=
  fsCells_eq_zero_of_generates
    (normalizationSlideMap core hcore (restrictedExtra extra p))
    (normalizationSlideMap core hcore (restrictedExtra extra t))
    (pairInclusion core extra hpt) (normalizedInclusion core hcore extra hpt)
    (slide_chain_square core hcore extra hpt) hzero
    (normalizationSlideMap_generates core hcore (restrictedExtra extra p)) hx

/-- The full actual replacement preserves every zero inclusion between
positive stages. All three required chain squares have been proved. -/
theorem relativeReplacement_preserves_zero
    (hzero : ∀ x, FSIsFoxCycle (rawPresentation core (restrictedExtra extra p)) x →
      (rawInclusion core extra hpt).cells x = 0)
    {x} (hx : FSIsFoxCycle (restrictedBlockPresentation core hcore extra p) x) :
    (blockInclusion core hcore extra hpt).cells x = 0 := by
  apply blockInclusion_preserves_zero core hcore extra hpt ?_ hx
  intro y hy
  apply slide_preserves_zero core hcore extra hpt ?_ hy
  intro z hz
  exact ruleOne_preserves_zero core extra hpt hzero hz

end FiniteChains.RelativeNormalForm
