import RequestProject.RelativeAmbientTerminal

/-! Concrete fixed-core chains in one ambient alphabet. Their fields
describe actual relators and actual coefficient maps; the replacement
and terminal conclusions used below are already proved constructions.
 -/

noncomputable section
open scoped Classical

namespace FiniteChains.RelativeNormalForm
open Davis Davis.Genus BlockFamily

variable {A C : Type} (core : C → FreeGroup A)

def stageCellEquivFull {S : Type} (p : S → Prop) (hall : ∀ s, p s) :
    (C ⊕ {s // p s}) ≃ (C ⊕ S) where
  toFun := Sum.map id Subtype.val
  invFun := Sum.map id (fun s => ⟨s, hall s⟩)
  left_inv := by rintro (c | ⟨s, hs⟩) <;> rfl
  right_inv := by rintro (c | s) <;> rfl

theorem stageIntoFull_generates {Z S : Type} (extra : S → FreeGroup (A ⊕ Z))
    (p : S → Prop) (hall : ∀ s, p s) : FSGenerates (stageIntoFull core extra p) := by
  exact PresInclusionFS.relabel_generates _ _ (Equiv.refl _)
    (stageCellEquivFull (C := C) p hall) (by
      intro j
      cases j <;> simp [rawPresentation, restrictedExtra, stageCellEquivFull])

def fullIntoStage {Z S : Type} (extra : S → FreeGroup (A ⊕ Z))
    (p : S → Prop) (hall : ∀ s, p s) :
    PresMorFS (rawPresentation core extra) (rawPresentation core (restrictedExtra extra p)) :=
  PresInclusionFS.mor _ _ id (stageCellEquivFull (C := C) p hall).symm
    Function.injective_id (stageCellEquivFull (C := C) p hall).symm.injective (by
      intro j
      cases j <;> simp [rawPresentation, restrictedExtra, stageCellEquivFull])

theorem fullIntoStage_generates {Z S : Type} (extra : S → FreeGroup (A ⊕ Z))
    (p : S → Prop) (hall : ∀ s, p s) : FSGenerates (fullIntoStage core extra p hall) := by
  exact PresInclusionFS.relabel_generates _ _ (Equiv.refl _)
    (stageCellEquivFull (C := C) p hall).symm (by
      intro j
      cases j <;> simp [rawPresentation, restrictedExtra, stageCellEquivFull])

theorem rawInclusion_factor_full {Z S : Type} (extra : S → FreeGroup (A ⊕ Z))
    {p t : S → Prop} (hpt : ∀ s, p s → t s) (hall : ∀ s, t s)
    (x : (C ⊕ {s // p s}) →₀ MonoidAlgebra ℤ
      (PresGroup (rawPresentation core (restrictedExtra extra p)))) :
    (rawInclusion core extra hpt).cells x =
      (fullIntoStage core extra t hall).cells ((stageIntoFull core extra p).cells x) := by
  have hg : (rawInclusion core extra hpt).hom =
      (fullIntoStage core extra t hall).hom.comp (stageIntoFull core extra p).hom := by
    apply MonoidHom.ext
    intro z
    induction z using QuotientGroup.induction_on with
    | H w => change QuotientGroup.mk (FreeGroup.map id w) =
        QuotientGroup.mk (FreeGroup.map id (FreeGroup.map id w)); simp
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [PresMorFS.cells_add, PresMorFS.cells_add, PresMorFS.cells_add, hx, hy]
  | single j a =>
      change PresInclusionFS.cells _ _ _ _ _ (Finsupp.single j a) =
        PresInclusionFS.cells _ _ _ _ _ (PresInclusionFS.cells _ _ _ _ _ (Finsupp.single j a))
      rw [PresInclusionFS.cells_single, PresInclusionFS.cells_single, PresInclusionFS.cells_single]
      have hj : oldCellIncl hpt j = (stageCellEquivFull (C := C) t hall).symm
          (Sum.map id Subtype.val j) := by cases j <;> rfl
      rw [hj]
      congr 1
      change MonoidAlgebra.mapDomainRingHom ℤ (rawInclusion core extra hpt).hom a =
        MonoidAlgebra.mapDomainRingHom ℤ (fullIntoStage core extra t hall).hom
          (MonoidAlgebra.mapDomainRingHom ℤ (stageIntoFull core extra p).hom a)
      rw [BlockMor.mapDomainRingHom_comp', ← hg]

/-- There are `n+1` positive stages after the unchanged core. The last
stage contains every ambient extra relator. All alphabets may be infinite. -/
structure AmbientChain (n : ℕ) where
  extraGen : Type
  extraCell : Type
  fresh : extraGen
  rel : extraCell → FreeGroup (A ⊕ extraGen)
  stage : ℕ → extraCell → Prop
  saturated : ∀ i, n ≤ i → ∀ s, stage i s
  mono : ∀ i s, stage i s → stage (i + 1) s
  strict : ∀ i, i < n → ∃ s, stage (i + 1) s ∧ ¬ stage i s
  cockcroft : ∀ i, FSIsCockcroft (rawPresentation core (restrictedExtra rel (stage i)))
  core_trivial : ∀ i a,
    (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) :
      PresGroup (rawPresentation core (restrictedExtra rel (stage i)))) = 1
  zero : ∀ i, i < n → ∀ x,
    FSIsFoxCycle (rawPresentation core (restrictedExtra rel (stage i))) x →
      (rawInclusion core rel (mono i)).cells x = 0

namespace AmbientChain
variable {core} {n : ℕ} (c : AmbientChain core n)

theorem full_cockcroft : FSIsCockcroft (rawPresentation core c.rel) :=
  fsIsCockcroft_of_generates (stageIntoFull core c.rel (c.stage n))
    (stageIntoFull_generates core c.rel (c.stage n) (c.saturated n le_rfl)) (c.cockcroft n)

theorem full_core_trivial (a : A) :
    (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup (rawPresentation core c.rel)) = 1 := by
  have h := congrArg (stageIntoFull core c.rel (c.stage n)).hom (c.core_trivial n a)
  change QuotientGroup.mk (FreeGroup.map id (FreeGroup.of (Sum.inl a))) =
    (stageIntoFull core c.rel (c.stage n)).hom 1 at h
  simpa only [FreeGroup.map.id, map_one] using h

/-- A literal initial pair, such as the actual FS `relY`, seeds the
induction. No replacement or terminal hypotheses are part of this input. -/
def initial {Z S : Type} (z : Z) (extra : S → FreeGroup (A ⊕ Z))
    (hc : FSIsCockcroft (rawPresentation core extra))
    (ht : ∀ a : A,
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup (rawPresentation core extra)) = 1) :
    AmbientChain core 0 where
  extraGen := Z
  extraCell := S
  fresh := z
  rel := extra
  stage := fun _ _ => True
  saturated := by intros; trivial
  mono := by intros; trivial
  strict := by intro i hi; omega
  cockcroft := fun _ => fsIsCockcroft_of_generates (fullIntoStage core extra _ (fun _ => trivial))
    (fullIntoStage_generates core extra _ (fun _ => trivial)) hc
  core_trivial := by
    intro i a
    have h := congrArg (fullIntoStage core extra (fun _ => True) (fun _ => trivial)).hom (ht a)
    change QuotientGroup.mk (FreeGroup.map id (FreeGroup.of (Sum.inl a))) =
      (fullIntoStage core extra (fun _ => True) (fun _ => trivial)).hom 1 at h
    simpa only [FreeGroup.map.id, map_one] using h
  zero := by intro i hi; omega

variable (hcore : Function.Surjective (expMatrix core))

def stepStage (i : ℕ) : NextExtraCell core hcore c.rel → Prop :=
  if i ≤ n then nextPredicate core hcore c.rel (c.stage i) else fun _ => True

theorem stepStage_eq_of_le (i : ℕ) (hi : i ≤ n) :
    c.stepStage hcore i = nextPredicate core hcore c.rel (c.stage i) := if_pos hi

theorem stepStage_eq_of_not_le (i : ℕ) (hi : ¬ i ≤ n) :
    c.stepStage hcore i = fun _ => True := if_neg hi

theorem stepStage_mono (i : ℕ) : ∀ s,
    c.stepStage hcore i s → c.stepStage hcore (i + 1) s := by
  intro s hs
  by_cases hi : i + 1 ≤ n
  · simp only [stepStage, if_pos hi, if_pos (by omega : i ≤ n)] at *
    exact nextPredicate_mono core hcore c.rel (c.mono i) s hs
  · simp only [stepStage, if_neg hi]

theorem stepStage_strict (i : ℕ) (hi : i < n + 1) :
    ∃ s, c.stepStage hcore (i + 1) s ∧ ¬ c.stepStage hcore i s := by
  by_cases hin : i < n
  · obtain ⟨s, hs, hsp⟩ := c.strict i hin
    simpa only [stepStage, if_pos (by omega : i ≤ n), if_pos (by omega : i + 1 ≤ n)] using
      nextStage_strict core hcore c.rel (p := c.stage i) (t := c.stage (i + 1)) s hs hsp
  · have he : i = n := by omega
    subst i
    refine ⟨Sum.inr (c.fresh, false), ?_, ?_⟩
    · simp [stepStage]
    · simp [stepStage, nextPredicate]

theorem lastStage_eq : c.stage n = fun _ => True := by
  funext s
  exact propext ⟨fun _ => trivial, fun _ => c.saturated n le_rfl s⟩

theorem stepStage_zero (hinj : Function.Injective (expMatrix core))
    (i : ℕ) (hi : i < n + 1) (x :
      (C ⊕ {s // c.stepStage hcore i s}) →₀ MonoidAlgebra ℤ
        (PresGroup (rawPresentation core (restrictedExtra
          (nextExtra core hcore c.rel) (c.stepStage hcore i)))))
    (hx : FSIsFoxCycle (rawPresentation core (restrictedExtra
      (nextExtra core hcore c.rel) (c.stepStage hcore i))) x) :
    (rawInclusion core (nextExtra core hcore c.rel) (c.stepStage_mono hcore i)).cells x = 0 := by
  let P (p t : NextExtraCell core hcore c.rel → Prop) : Prop :=
    ∀ (hpt : ∀ s, p s → t s)
      (y : (C ⊕ {s // p s}) →₀ MonoidAlgebra ℤ
        (PresGroup (rawPresentation core (restrictedExtra (nextExtra core hcore c.rel) p)))),
      FSIsFoxCycle (rawPresentation core (restrictedExtra (nextExtra core hcore c.rel) p)) y →
        (rawInclusion core (nextExtra core hcore c.rel) hpt).cells y = 0
  have hz : P (c.stepStage hcore i) (c.stepStage hcore (i + 1)) := by
    by_cases hin : i < n
    · rw [c.stepStage_eq_of_le hcore i (by omega),
        c.stepStage_eq_of_le hcore (i + 1) (by omega)]
      intro hpt y hy
      exact nextStage_preserves_zero core hcore c.rel (c.mono i) (c.zero i hin) hy
    · have he : i = n := by omega
      subst i
      rw [c.stepStage_eq_of_le hcore n le_rfl,
        c.stepStage_eq_of_not_le hcore (n + 1) (by omega), c.lastStage_eq]
      intro hpt y hy
      rw [rawInclusion_factor_full core (nextExtra core hcore c.rel) hpt (fun _ => trivial)]
      have ht := (nextTerminal_conclusions core hcore c.rel hinj c.full_cockcroft
        c.full_core_trivial).2 y hy
      rw [ht, PresMorFS.cells_zero]
  exact hz (c.stepStage_mono hcore i) x hx

/-- The simultaneous fixed-core step `(D,L₁,…,Lₘ)` to
`(D,T L₁,…,T Lₘ,Q Lₘ)`, in actual repeated-use ambient coordinates. -/
def step (hinj : Function.Injective (expMatrix core)) : AmbientChain core (n + 1) where
  extraGen := NextExtraGen core hcore c.rel
  extraCell := NextExtraCell core hcore c.rel
  fresh := Sum.inl (c.fresh, false)
  rel := nextExtra core hcore c.rel
  stage := c.stepStage hcore
  saturated := by
    intro i hi s
    simp only [stepStage, if_neg (by omega : ¬ i ≤ n)]
  mono := c.stepStage_mono hcore
  strict := c.stepStage_strict hcore
  cockcroft := by
    intro i
    let P (p : NextExtraCell core hcore c.rel → Prop) : Prop :=
      FSIsCockcroft (rawPresentation core (restrictedExtra (nextExtra core hcore c.rel) p))
    change P (c.stepStage hcore i)
    by_cases hi : i ≤ n
    · rw [c.stepStage_eq_of_le hcore i hi]
      exact nextStage_cockcroft core hcore c.rel (c.stage i) (c.cockcroft i)
    · rw [c.stepStage_eq_of_not_le hcore i hi]
      exact fsIsCockcroft_of_generates
        (fullIntoStage core (nextExtra core hcore c.rel) (fun _ => True) (fun _ => trivial))
        (fullIntoStage_generates core (nextExtra core hcore c.rel) (fun _ => True) (fun _ => trivial))
        (nextTerminal_conclusions core hcore c.rel hinj c.full_cockcroft c.full_core_trivial).1
  core_trivial := by
    intro i a
    let P (p : NextExtraCell core hcore c.rel → Prop) : Prop :=
      (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup
        (rawPresentation core (restrictedExtra (nextExtra core hcore c.rel) p))) = 1
    change P (c.stepStage hcore i)
    by_cases hi : i ≤ n
    · rw [c.stepStage_eq_of_le hcore i hi]
      exact nextStage_core_trivial core hcore c.rel (c.stage i) (c.core_trivial i) a
    · rw [c.stepStage_eq_of_not_le hcore i hi]
      have h := congrArg (fullIntoStage core (nextExtra core hcore c.rel)
        (fun _ => True) (fun _ => trivial)).hom
        (nextFull_core_trivial core hcore c.rel c.full_core_trivial a)
      change QuotientGroup.mk (FreeGroup.map id (FreeGroup.of (Sum.inl a))) =
        (fullIntoStage core (nextExtra core hcore c.rel) (fun _ => True) (fun _ => trivial)).hom 1 at h
      exact (show (QuotientGroup.mk (FreeGroup.of (Sum.inl a)) : PresGroup
        (rawPresentation core (restrictedExtra (nextExtra core hcore c.rel) (fun _ => True)))) = 1
        from by simpa only [FreeGroup.map.id, map_one] using h)
  zero := c.stepStage_zero hcore hinj

end AmbientChain

/-- Iterating the actual construction produces all finite chain lengths
over the same core. Only the initial concrete relative presentation is
an argument; all replacement and terminal obligations are discharged. -/
def ambientChains (hcore : Function.Bijective (expMatrix core))
    (initial : AmbientChain core 0) : (n : ℕ) → AmbientChain core n
  | 0 => initial
  | n + 1 => (ambientChains hcore initial n).step hcore.2 hcore.1

end FiniteChains.RelativeNormalForm
