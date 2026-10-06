module

public import RequestProject.RelativeAmbientReplacement

@[expose] public section

/-! The appended terminal stage in the ambient indexing used for the
next iteration. No terminal vanishing or Cockcroft hypothesis is introduced.
Awaiting final Lean verification. -/

noncomputable section
open scoped Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.RelativeNormalForm
open Davis Davis.Genus BlockFamily

variable {A C Z S : Type} (core : C → FreeGroup A)
  (hcore : Function.Surjective (expMatrix core))
  (extra : S → FreeGroup (A ⊕ Z))

def fullNextCell :
    (C ⊕ (Σ s, NamedSpineRel (normalizedGenus core hcore extra s))) ≃
      (C ⊕ {s // nextPredicate core hcore extra (fun _ => True) s}) where
  toFun
    | Sum.inl c => Sum.inl c
    | Sum.inr m => Sum.inr ⟨Sum.inl m, trivial⟩
  invFun
    | Sum.inl c => Sum.inl c
    | Sum.inr ⟨Sum.inl m, _⟩ => Sum.inr m
    | Sum.inr ⟨Sum.inr _, h⟩ => h.elim
  left_inv := by rintro (c | m) <;> rfl
  right_inv := by rintro (c | ⟨m | k, h⟩); rfl; rfl; exact h.elim

theorem fullNext_rel (j : C ⊕ (Σ s, NamedSpineRel (normalizedGenus core hcore extra s))) :
    nextStage core hcore extra (fun _ => True) (fullNextCell core hcore extra j) =
      FreeGroup.map (flattenBlockGen core hcore extra) (blockPresentation core hcore extra j) := by
  cases j with
  | inr m => rfl
  | inl c =>
      change FreeGroup.map Sum.inl (core c) = FreeGroup.map (flattenBlockGen core hcore extra)
        (FreeGroup.map Sum.inl (FreeGroup.map Sum.inl (core c)))
      have h : ((FreeGroup.map (flattenBlockGen core hcore extra)).comp
          (FreeGroup.map Sum.inl)).comp (FreeGroup.map Sum.inl) = FreeGroup.map Sum.inl := by
        apply FreeGroup.ext_hom
        intro a
        rfl
      exact (DFunLike.congr_fun h (core c)).symm

def fullNextMap : PresMorFS (blockPresentation core hcore extra)
    (nextStage core hcore extra (fun _ => True)) :=
  PresInclusionFS.mor _ _ (flattenBlockGen core hcore extra) (fullNextCell core hcore extra)
    (flattenBlockGen core hcore extra).injective (fullNextCell core hcore extra).injective
    (fullNext_rel core hcore extra)

theorem fullNextMap_generates : FSGenerates (fullNextMap core hcore extra) :=
  PresInclusionFS.relabel_generates _ _ (flattenBlockGen core hcore extra)
    (fullNextCell core hcore extra) (fullNext_rel core hcore extra)

def terminalNextCell :
    ((C ⊕ (Σ s, NamedSpineRel (normalizedGenus core hcore extra s))) ⊕ (Z × Bool)) ≃
      (C ⊕ NextExtraCell core hcore extra) := Equiv.sumAssoc _ _ _

theorem terminalNext_rel
    (j : (C ⊕ (Σ s, NamedSpineRel (normalizedGenus core hcore extra s))) ⊕ (Z × Bool)) :
    rawPresentation core (nextExtra core hcore extra) (terminalNextCell core hcore extra j) =
      FreeGroup.map (flattenBlockGen core hcore extra) (terminalPresentation core hcore extra j) := by
  rcases j with (c | m) | k
  · exact fullNext_rel core hcore extra (Sum.inl c)
  · rfl
  · rfl

def terminalNextMap : PresMorFS (terminalPresentation core hcore extra)
    (rawPresentation core (nextExtra core hcore extra)) :=
  PresInclusionFS.mor _ _ (flattenBlockGen core hcore extra) (terminalNextCell core hcore extra)
    (flattenBlockGen core hcore extra).injective (terminalNextCell core hcore extra).injective
    (terminalNext_rel core hcore extra)

theorem terminalNextMap_generates : FSGenerates (terminalNextMap core hcore extra) :=
  PresInclusionFS.relabel_generates _ _ (flattenBlockGen core hcore extra)
    (terminalNextCell core hcore extra) (terminalNext_rel core hcore extra)

/-- A selected stage includes into the full presentation by forgetting
only the proof attached to its extra-cell labels. -/
def stageIntoFull {B T : Type} (r : T → FreeGroup (A ⊕ B)) (p : T → Prop) :
    PresMorFS (rawPresentation core (restrictedExtra r p)) (rawPresentation core r) :=
  PresInclusionFS.mor _ _ id (Sum.map id Subtype.val) Function.injective_id
    (Function.Injective.sumMap Function.injective_id Subtype.val_injective) (by
      intro j
      cases j <;> simp [rawPresentation, restrictedExtra])

theorem nextTerminal_square
    (x : (C ⊕ (Σ s, NamedSpineRel (normalizedGenus core hcore extra s))) →₀
      MonoidAlgebra ℤ (PresGroup (blockPresentation core hcore extra))) :
    (stageIntoFull core (nextExtra core hcore extra)
      (nextPredicate core hcore extra (fun _ => True))).cells ((fullNextMap core hcore extra).cells x) =
    (terminalNextMap core hcore extra).cells ((relativeTerminalMap core hcore extra).cells x) := by
  have hgroup : (stageIntoFull core (nextExtra core hcore extra)
      (nextPredicate core hcore extra (fun _ => True))).hom.comp (fullNextMap core hcore extra).hom =
    (terminalNextMap core hcore extra).hom.comp (relativeTerminalMap core hcore extra).hom := by
    apply MonoidHom.ext
    intro g
    induction g using QuotientGroup.induction_on with
    | H w =>
        change QuotientGroup.mk (FreeGroup.map id (FreeGroup.map
          (flattenBlockGen core hcore extra) w)) =
          QuotientGroup.mk (FreeGroup.map (flattenBlockGen core hcore extra) w)
        simp
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [PresMorFS.cells_add, PresMorFS.cells_add, PresMorFS.cells_add,
        PresMorFS.cells_add, hx, hy]
  | single j a =>
      change PresInclusionFS.cells _ _ _ _ _
        (PresInclusionFS.cells _ _ _ _ _ (Finsupp.single j a)) =
        PresInclusionFS.cells _ _ _ _ _ (addRelsCellsFS _ _ (Finsupp.single j a))
      rw [PresInclusionFS.cells_single, PresInclusionFS.cells_single,
        addRelsCellsFS_single, PresInclusionFS.cells_single]
      have hj : Sum.map id Subtype.val (fullNextCell core hcore extra j) =
          terminalNextCell core hcore extra (Sum.inl j) := by cases j <;> rfl
      rw [hj]
      congr 1
      change MonoidAlgebra.mapDomainRingHom ℤ
        (stageIntoFull core (nextExtra core hcore extra)
          (nextPredicate core hcore extra (fun _ => True))).hom
        (MonoidAlgebra.mapDomainRingHom ℤ (fullNextMap core hcore extra).hom a) =
        MonoidAlgebra.mapDomainRingHom ℤ (terminalNextMap core hcore extra).hom
          (MonoidAlgebra.mapDomainRingHom ℤ (relativeTerminalMap core hcore extra).hom a)
      erw [BlockMor.mapDomainRingHom_comp', BlockMor.mapDomainRingHom_comp', hgroup]

/-- The next ambient presentation is Cockcroft and the last replaced
stage maps to it by zero on every actual supported two-cycle. -/
theorem nextTerminal_conclusions
    (hinj : Function.Injective (expMatrix core))
    (hP : FSIsCockcroft (rawPresentation core extra))
    (htriv : ∀ a : A,
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup (rawPresentation core extra)) = 1) :
    FSIsCockcroft (rawPresentation core (nextExtra core hcore extra)) ∧
      (∀ x, FSIsFoxCycle (nextStage core hcore extra (fun _ => True)) x →
        (stageIntoFull core (nextExtra core hcore extra)
          (nextPredicate core hcore extra (fun _ => True))).cells x = 0) := by
  obtain ⟨hc, hz⟩ := relativeTerminal_conclusions core hcore extra hinj hP htriv
  refine ⟨fsIsCockcroft_of_generates (terminalNextMap core hcore extra)
    (terminalNextMap_generates core hcore extra) hc, ?_⟩
  intro x hx
  apply fsCells_eq_zero_of_generates (fullNextMap core hcore extra)
    (terminalNextMap core hcore extra) (relativeTerminalMap core hcore extra)
    (stageIntoFull core (nextExtra core hcore extra)
      (nextPredicate core hcore extra (fun _ => True)))
    (nextTerminal_square core hcore extra) hz (fullNextMap_generates core hcore extra) hx

theorem block_core_trivial
    (htriv : ∀ a : A,
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup (rawPresentation core extra)) = 1)
    (a : A) :
    (QuotientGroup.mk (FreeGroup.of (Sum.inl (Sum.inl a))) :
      PresGroup (blockPresentation core hcore extra)) = 1 := by
  have hn := normalized_core_trivial core hcore extra htriv a
  have h := congrArg (blockStructuralMap core hcore extra).hom hn
  change (QuotientGroup.mk (FreeGroup.map Sum.inl (FreeGroup.of (Sum.inl a))) :
      PresGroup (blockPresentation core hcore extra)) =
    (blockStructuralMap core hcore extra).hom 1 at h
  simp only [FreeGroup.map.of, map_one] at h
  convert h using 1 <;> rfl

theorem nextStage_core_trivial (p : S → Prop)
    (htriv : ∀ a : A,
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) :
        PresGroup (rawPresentation core (restrictedExtra extra p))) = 1) (a : A) :
    (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup (nextStage core hcore extra p)) = 1 := by
  have h := congrArg (stageNextMap core hcore extra p).hom
    (block_core_trivial core hcore (restrictedExtra extra p) htriv a)
  change QuotientGroup.mk (FreeGroup.map (stageNextGen core hcore extra p)
    (FreeGroup.of (Sum.inl (Sum.inl a)))) = (stageNextMap core hcore extra p).hom 1 at h
  simpa only [FreeGroup.map.of, stageNextGen, map_one] using h

theorem nextFull_core_trivial
    (htriv : ∀ a : A,
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup (rawPresentation core extra)) = 1)
    (a : A) :
    (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) :
      PresGroup (rawPresentation core (nextExtra core hcore extra))) = 1 := by
  have h := congrArg ((terminalNextMap core hcore extra).hom.comp
    (relativeTerminalMap core hcore extra).hom) (block_core_trivial core hcore extra htriv a)
  change QuotientGroup.mk (FreeGroup.map (flattenBlockGen core hcore extra)
    (FreeGroup.of (Sum.inl (Sum.inl a)))) =
      ((terminalNextMap core hcore extra).hom.comp (relativeTerminalMap core hcore extra).hom) 1 at h
  simp only [FreeGroup.map.of, map_one] at h
  convert h using 1 <;> rfl

/-- Acyclicity of the core is used through its actual supported exponent
matrix. It does not assert that the core has trivial second homotopy group. -/
theorem core_fsIsCockcroft (hinj : Function.Injective (expMatrix core)) : FSIsCockcroft core := by
  intro x hx
  have h : x.mapRange (augPres core) (map_zero _) = 0 := by
    apply hinj
    rw [expMatrix_augmentation, hx, map_zero]
    exact Finsupp.mapRange_zero
  intro c
  exact DFunLike.congr_fun h c

def coreIntoRaw : PresMorFS core (rawPresentation core extra) :=
  PresInclusionFS.mor _ _ Sum.inl Sum.inl Sum.inl_injective Sum.inl_injective (fun _ => rfl)

theorem coreIntoRaw_zero (hinj : Function.Injective (expMatrix core))
    (htriv : ∀ a : A,
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup (rawPresentation core extra)) = 1)
    (x : C →₀ MonoidAlgebra ℤ (PresGroup core)) (hx : FSIsFoxCycle core x) :
    (coreIntoRaw core extra).cells x = 0 := by
  apply fsCells_eq_zero_of_isCockcroft_of_hom_trivial (coreIntoRaw core extra)
    (core_fsIsCockcroft core hinj) ?_ x hx
  apply hom_eq_one_of_gens
  intro a
  exact htriv a

end FiniteChains.RelativeNormalForm
