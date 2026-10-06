import RequestProject.RelativeNormalizedWords

/-! Restrictions of the single ambient normalization. No correction or
commutator factorization is re-chosen when a stage is restricted.
The actual genus relators respect the resulting labelled inclusions.

-/

noncomputable section
open scoped Classical

namespace FiniteChains.RelativeNormalForm

open Davis Davis.Genus BlockFamily

variable {A C Z S : Type} (core : C → FreeGroup A)
  (hcore : Function.Surjective (expMatrix core))
  (extra : S → FreeGroup (A ⊕ Z))

def restrictedPresentation (p : S → Prop) : C ⊕ {s // p s} → FreeGroup (PairGen A Z) :=
  Sum.elim (fun c => FreeGroup.map Sum.inl (core c))
    (fun s => normalizedWord core hcore (extra s.val))

def restrictedGenus (p : S → Prop) (s : {s // p s}) : ℕ :=
  normalizedGenus core hcore extra s.val

instance restrictedGenus_neZero (p : S → Prop) (s : {s // p s}) :
    NeZero (restrictedGenus core hcore extra p s) :=
  normalizedGenus_neZero core hcore extra s.val

def restrictedLoops (p : S → Prop) (s : {s // p s}) :
    Fin (restrictedGenus core hcore extra p s) × Bool → FreeGroup (PairGen A Z) :=
  normalizedLoops core hcore extra s.val

theorem restrictedPresentation_surface (p : S → Prop) (s : {s // p s}) :
    restrictedPresentation core hcore extra p (Sum.inr s) =
      commWord (restrictedLoops core hcore extra p s)
        (finitePairs (restrictedGenus core hcore extra p s)) :=
  normalizedPresentation_surface core hcore extra s.val

def restrictedBlockPresentation (p : S → Prop) :
    C ⊕ (Σ s : {s // p s}, NamedSpineRel (restrictedGenus core hcore extra p s)) →
      FreeGroup (PairGen A Z ⊕
        (Σ s : {s // p s}, SpinePresentationGen (restrictedGenus core hcore extra p s))) :=
  substPresF (restrictedPresentation core hcore extra p)
    (familyFiniteSpineWordBlock (restrictedGenus core hcore extra p)
      (restrictedLoops core hcore extra p))

def restrictedStructuralMap (p : S → Prop) :
    PresMorFS (restrictedPresentation core hcore extra p)
      (restrictedBlockPresentation core hcore extra p) := by
  let dSrc : DecidableEq (PairGen A Z) := inferInstance
  let dTgt : DecidableEq (PairGen A Z ⊕ (Σ s : {s // p s},
      SpinePresentationGen (restrictedGenus core hcore extra p s))) := inferInstance
  letI : DecidableEq (PairGen A Z) := Classical.decEq _
  letI : DecidableEq {s // p s} := Classical.decEq _
  let dFamilyTgt : DecidableEq (PairGen A Z ⊕ (Σ s : {s // p s},
      SpinePresentationGen (restrictedGenus core hcore extra p s))) :=
    @instDecidableEqSum _ _ (Classical.decEq _) inferInstance
  exact @PresMorFS.redecide _ _ _ _ (Classical.decEq _) dFamilyTgt _ _
    (finiteSpineFamilyStructuralMap (restrictedPresentation core hcore extra p)
    (restrictedGenus core hcore extra p) (restrictedLoops core hcore extra p)
    (restrictedPresentation_surface core hcore extra p)) dSrc dTgt

theorem restrictedStructuralMap_generates (p : S → Prop) :
    FSGenerates (restrictedStructuralMap core hcore extra p) := by
  let dSrc : DecidableEq (PairGen A Z) := inferInstance
  let dTgt : DecidableEq (PairGen A Z ⊕ (Σ s : {s // p s},
      SpinePresentationGen (restrictedGenus core hcore extra p s))) := inferInstance
  letI : DecidableEq (PairGen A Z) := Classical.decEq _
  letI : DecidableEq {s // p s} := Classical.decEq _
  let dFamilyTgt : DecidableEq (PairGen A Z ⊕ (Σ s : {s // p s},
      SpinePresentationGen (restrictedGenus core hcore extra p s))) :=
    @instDecidableEqSum _ _ (Classical.decEq _) inferInstance
  exact @FSGenerates.redecide _ _ _ _ (Classical.decEq _) dFamilyTgt _ _ _
    (finiteSpineFamilyStructuralMap_generates (restrictedPresentation core hcore extra p)
    (restrictedGenus core hcore extra p) (restrictedLoops core hcore extra p)
    (restrictedPresentation_surface core hcore extra p)) dSrc dTgt

variable {p t : S → Prop} (hpt : ∀ s, p s → t s)

def labelIncl (s : {s // p s}) : {s // t s} := ⟨s.val, hpt s.val s.property⟩

theorem labelIncl_injective : Function.Injective (labelIncl hpt) := by
  intro s s' h
  exact Subtype.ext (congrArg (fun x : {s // t s} => x.val) h)

def oldCellIncl : C ⊕ {s // p s} → C ⊕ {s // t s} := Sum.map id (labelIncl hpt)

theorem oldCellIncl_injective : Function.Injective (oldCellIncl (C := C) hpt) :=
  Function.Injective.sumMap Function.injective_id (labelIncl_injective hpt)

def blockGenIncl :
    (PairGen A Z ⊕ (Σ s : {s // p s}, SpinePresentationGen (restrictedGenus core hcore extra p s))) →
    (PairGen A Z ⊕ (Σ s : {s // t s}, SpinePresentationGen (restrictedGenus core hcore extra t s))) :=
  Sum.map id (fun z => ⟨labelIncl hpt z.1, z.2⟩)

def blockCellIncl :
    (C ⊕ (Σ s : {s // p s}, NamedSpineRel (restrictedGenus core hcore extra p s))) →
    (C ⊕ (Σ s : {s // t s}, NamedSpineRel (restrictedGenus core hcore extra t s))) :=
  Sum.map id (fun m => ⟨labelIncl hpt m.1, m.2⟩)

private theorem sigma_labelIncl_injective {F : S → Type}
    : Function.Injective (fun z : Σ s : {s // p s}, F s.val =>
        (⟨labelIncl hpt z.1, z.2⟩ : Σ s : {s // t s}, F s.val)) := by
  rintro ⟨s, x⟩ ⟨s', x'⟩ h
  have hs : s = s' := labelIncl_injective hpt (congrArg Sigma.fst h)
  subst s'
  have hx : x = x' := eq_of_heq (Sigma.mk.inj h).2
  subst x'
  rfl

theorem blockGenIncl_injective :
    Function.Injective (blockGenIncl core hcore extra hpt) :=
  Function.Injective.sumMap Function.injective_id
    (sigma_labelIncl_injective (F := fun s => SpinePresentationGen
      (normalizedGenus core hcore extra s)) hpt)

theorem blockCellIncl_injective :
    Function.Injective (blockCellIncl core hcore extra hpt) :=
  Function.Injective.sumMap Function.injective_id
    (sigma_labelIncl_injective (F := fun s => NamedSpineRel
      (normalizedGenus core hcore extra s)) hpt)

/-- Literal compatibility of the corrected relators, with the core fixed. -/
theorem restrictedPresentation_incl (c : C ⊕ {s // p s}) :
    restrictedPresentation core hcore extra t (oldCellIncl hpt c) =
      restrictedPresentation core hcore extra p c := by
  cases c <;> rfl

theorem blockGenIncl_genEmb (s : {s // p s}) :
    (FreeGroup.map (blockGenIncl core hcore extra hpt)).comp
      (FreeGroup.map (genEmb (α := PairGen A Z)
        (Zt := fun r => SpinePresentationGen (restrictedGenus core hcore extra p r)) s)) =
    FreeGroup.map (genEmb (α := PairGen A Z)
      (Zt := fun r => SpinePresentationGen (restrictedGenus core hcore extra t r))
      (labelIncl hpt s)) := by
  apply FreeGroup.ext_hom
  intro x
  rw [MonoidHom.comp_apply, FreeGroup.map.of, FreeGroup.map.of]
  erw [FreeGroup.map.of]
  cases x <;> rfl

/-- Actual genus relators, not an abstract presentation assignment, respect
the same ambient-label inclusion. -/
theorem restrictedBlockPresentation_incl
    (m : C ⊕ (Σ s : {s // p s}, NamedSpineRel (restrictedGenus core hcore extra p s))) :
    restrictedBlockPresentation core hcore extra t (blockCellIncl core hcore extra hpt m) =
      FreeGroup.map (blockGenIncl core hcore extra hpt)
        (restrictedBlockPresentation core hcore extra p m) := by
  cases m with
  | inl c =>
      change FreeGroup.map Sum.inl (FreeGroup.map Sum.inl (core c)) =
        FreeGroup.map (blockGenIncl core hcore extra hpt)
          (FreeGroup.map Sum.inl (FreeGroup.map Sum.inl (core c)))
      have h : (FreeGroup.map (blockGenIncl core hcore extra hpt)).comp
          (FreeGroup.map Sum.inl) = FreeGroup.map Sum.inl := by
        apply FreeGroup.ext_hom
        intro x
        simp [blockGenIncl]
      exact (congrArg (fun f => f (FreeGroup.map Sum.inl (core c))) h).symm
  | inr m =>
      exact (congrArg (fun f => f
        (familyFiniteSpineWordBlock (restrictedGenus core hcore extra p)
          (restrictedLoops core hcore extra p) m.1 m.2))
        (blockGenIncl_genEmb core hcore extra hpt m.1)).symm

def normalizedGroupIncl : PresGroup (restrictedPresentation core hcore extra p) →*
    PresGroup (restrictedPresentation core hcore extra t) :=
  QuotientGroup.map _ _ (MonoidHom.id _) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨c, rfl⟩
    apply Subgroup.mem_comap.mpr
    change restrictedPresentation core hcore extra p c ∈ _
    rw [← restrictedPresentation_incl core hcore extra hpt c]
    exact Subgroup.subset_normalClosure ⟨oldCellIncl hpt c, rfl⟩)

def blockGroupIncl : PresGroup (restrictedBlockPresentation core hcore extra p) →*
    PresGroup (restrictedBlockPresentation core hcore extra t) :=
  QuotientGroup.map _ _ (FreeGroup.map (blockGenIncl core hcore extra hpt)) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨m, rfl⟩
    apply Subgroup.mem_comap.mpr
    rw [← restrictedBlockPresentation_incl core hcore extra hpt m]
    exact Subgroup.subset_normalClosure ⟨blockCellIncl core hcore extra hpt m, rfl⟩)

/-- The structural group square commutes for the actual restricted
replacement presentations. -/
theorem restrictedStructuralMap_group_square :
    (blockGroupIncl core hcore extra hpt).comp
      (restrictedStructuralMap core hcore extra p).hom =
    (restrictedStructuralMap core hcore extra t).hom.comp
      (normalizedGroupIncl core hcore extra hpt) := by
  ext a
  rfl

/-- A missing ambient relator supplies an actual new marked two-cell.
Thus restriction preserves strictness witnessed by a relator label. -/
theorem blockCellIncl_not_surjective (s : S) (hs : t s) (hsp : ¬ p s) :
    ¬ Function.Surjective (blockCellIncl core hcore extra hpt) := by
  intro hsurj
  have hq := (surfaceChoice core hcore (extra s)).genus_ge_two
  let m : NamedSpineRel (normalizedGenus core hcore extra s) :=
    Sum.inr (⟨0, by change 0 < (surfaceChoice core hcore (extra s)).genus; omega⟩, false)
  obtain ⟨x, hx⟩ := hsurj (Sum.inr ⟨⟨s, hs⟩, m⟩)
  cases x with
  | inl c => cases hx
  | inr x =>
      have he : x.1.val = s := congrArg (fun z => z.1.val) (Sum.inr.inj hx)
      exact hsp (he ▸ x.1.property)

end FiniteChains.RelativeNormalForm
