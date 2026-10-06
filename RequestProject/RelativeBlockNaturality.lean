import RequestProject.PresentationInclusionFinsupp
import RequestProject.RelativeNormalizedRestrictions

/-! Actual chain squares for restricted genus replacement. The filling
coefficients are the fixed marked-spine coefficients, transported by the
actual inclusion of stage groups. No commuting-square hypothesis is used.

-/

noncomputable section
open scoped Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.BlockFamily

variable {A C S : Type} {Z M : S → Type}
  (ρ : C ⊕ S → FreeGroup A) (b : ∀ s, M s → FreeGroup (A ⊕ Z s))
  (hfill : FilledF ρ b)
  (c : ∀ s, M s →₀ MonoidAlgebra ℤ (PresGroup (substPresF ρ b)))

theorem fsCellsF_single_extra (s : S) (a : MonoidAlgebra ℤ (PresGroup ρ)) :
    fsCellsF ρ b hfill c (Finsupp.single (Sum.inr s) a) =
      coeffF ρ b hfill a • fsSurfaceChain c s := by
  rw [fsCellsF, Finsupp.mapRange_single,
    ← Finsupp.smul_single_one (Sum.inr s) (coeffF ρ b hfill a),
    map_smul, fsCellsBase_single_inr]

end FiniteChains.BlockFamily

namespace FiniteChains.RelativeNormalForm
open Davis Davis.Genus BlockFamily

variable {A C Z S : Type} (core : C → FreeGroup A)
  (hcore : Function.Surjective (expMatrix core))
  (extra : S → FreeGroup (A ⊕ Z))
  {p t : S → Prop} (hpt : ∀ s, p s → t s)

def normalizedInclusion : PresMorFS (restrictedPresentation core hcore extra p)
    (restrictedPresentation core hcore extra t) :=
  PresInclusionFS.mor _ _ id (oldCellIncl hpt) Function.injective_id
    (oldCellIncl_injective hpt) (by
      intro j
      simpa only [FreeGroup.map.id] using restrictedPresentation_incl core hcore extra hpt j)

def blockInclusion : PresMorFS (restrictedBlockPresentation core hcore extra p)
    (restrictedBlockPresentation core hcore extra t) :=
  PresInclusionFS.mor _ _ (blockGenIncl core hcore extra hpt)
    (blockCellIncl core hcore extra hpt)
    (blockGenIncl_injective core hcore extra hpt)
    (blockCellIncl_injective core hcore extra hpt)
    (restrictedBlockPresentation_incl core hcore extra hpt)

theorem blockInclusion_structural_group_square :
    (blockInclusion core hcore extra hpt).hom.comp
      (restrictedStructuralMap core hcore extra p).hom =
    (restrictedStructuralMap core hcore extra t).hom.comp
      (normalizedInclusion core hcore extra hpt).hom := by
  ext a
  change QuotientGroup.mk (FreeGroup.map (blockGenIncl core hcore extra hpt)
      (FreeGroup.map Sum.inl (FreeGroup.of a))) =
    QuotientGroup.mk (FreeGroup.map Sum.inl (FreeGroup.map id (FreeGroup.of a)))
  simp [blockGenIncl]

theorem blockInclusion_marked_group_square (s : {s // p s}) :
    (blockInclusion core hcore extra hpt).hom.comp
      (finiteSpineFamilyMarkedHom (restrictedPresentation core hcore extra p)
        (restrictedGenus core hcore extra p) (restrictedLoops core hcore extra p) s) =
    finiteSpineFamilyMarkedHom (restrictedPresentation core hcore extra t)
      (restrictedGenus core hcore extra t) (restrictedLoops core hcore extra t)
      (labelIncl hpt s) := by
  apply MonoidHom.ext
  intro g
  induction g using QuotientGroup.induction_on with
  | H w =>
      exact congrArg QuotientGroup.mk (congrArg
        (fun f => f (blockSubst
          (Zt := fun s => SpinePresentationGen (restrictedGenus core hcore extra p s))
          (restrictedLoops core hcore extra p) s w))
        (blockGenIncl_genEmb core hcore extra hpt s))

/-- The coefficient choices of a block are carried to the identical choices
in every later stage; no new filling is selected. -/
theorem blockInclusion_filling (s : {s // p s}) :
    (finiteSpineFamilyFilling (restrictedPresentation core hcore extra p)
      (restrictedGenus core hcore extra p) (restrictedLoops core hcore extra p) s).mapRange
        (MonoidAlgebra.mapDomainRingHom ℤ (blockInclusion core hcore extra hpt).hom) (map_zero _) =
    finiteSpineFamilyFilling (restrictedPresentation core hcore extra t)
      (restrictedGenus core hcore extra t) (restrictedLoops core hcore extra t)
      (labelIncl hpt s) := by
  ext m : 1
  change MonoidAlgebra.mapDomainRingHom ℤ (blockInclusion core hcore extra hpt).hom
      (MonoidAlgebra.mapDomainRingHom ℤ
        (finiteSpineFamilyMarkedHom (restrictedPresentation core hcore extra p)
          (restrictedGenus core hcore extra p) (restrictedLoops core hcore extra p) s)
        (markedSpineFilling (restrictedGenus core hcore extra p s) m)) = _
  erw [BlockMor.mapDomainRingHom_comp']
  erw [blockInclusion_marked_group_square]
  rfl

theorem blockInclusion_surface_chain (s : {s // p s})
    (x : NamedSpineRel (restrictedGenus core hcore extra p s) →₀
      MonoidAlgebra ℤ (PresGroup (restrictedBlockPresentation core hcore extra p))) :
    (blockInclusion core hcore extra hpt).cells
      (Finsupp.mapDomain (fun m => Sum.inr ⟨s, m⟩) x) =
    Finsupp.mapDomain (fun m => Sum.inr ⟨labelIncl hpt s, m⟩)
      (x.mapRange (MonoidAlgebra.mapDomainRingHom ℤ
        (blockInclusion core hcore extra hpt).hom) (map_zero _)) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [Finsupp.mapDomain_add, PresMorFS.cells_add, hx, hy,
        Finsupp.mapRange_add', Finsupp.mapDomain_add]
  | single m a =>
      simp only [Finsupp.mapDomain_single, Finsupp.mapRange_single]
      change Finsupp.mapDomain (blockCellIncl core hcore extra hpt)
        ((Finsupp.single (Sum.inr ⟨s, m⟩) a).mapRange _ _) = _
      rw [Finsupp.mapRange_single, Finsupp.mapDomain_single]
      rfl

/-- The actual two-chain square commutes. This supplies the square required
by zero-map propagation in the fixed-core induction. -/
theorem blockInclusion_structural_chain_square
    (x : (C ⊕ {s // p s}) →₀ MonoidAlgebra ℤ
      (PresGroup (restrictedPresentation core hcore extra p))) :
    (blockInclusion core hcore extra hpt).cells
      ((restrictedStructuralMap core hcore extra p).cells x) =
    (restrictedStructuralMap core hcore extra t).cells
      ((normalizedInclusion core hcore extra hpt).cells x) := by
  have hcoeff (a : MonoidAlgebra ℤ (PresGroup (restrictedPresentation core hcore extra p))) :
      MonoidAlgebra.mapDomainRingHom ℤ (blockInclusion core hcore extra hpt).hom
        (MonoidAlgebra.mapDomainRingHom ℤ (restrictedStructuralMap core hcore extra p).hom a) =
      MonoidAlgebra.mapDomainRingHom ℤ (restrictedStructuralMap core hcore extra t).hom
        (MonoidAlgebra.mapDomainRingHom ℤ (normalizedInclusion core hcore extra hpt).hom a) := by
    rw [BlockMor.mapDomainRingHom_comp', BlockMor.mapDomainRingHom_comp',
      blockInclusion_structural_group_square]
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [PresMorFS.cells_add, PresMorFS.cells_add, PresMorFS.cells_add,
        PresMorFS.cells_add, hx, hy]
  | single k a =>
      have hi := PresInclusionFS.cells_single
        (restrictedPresentation core hcore extra p) (restrictedPresentation core hcore extra t)
        id (oldCellIncl hpt)
        (fun j => by simpa only [FreeGroup.map.id] using
          restrictedPresentation_incl core hcore extra hpt j) k a
      change (normalizedInclusion core hcore extra hpt).cells (Finsupp.single k a) = _ at hi
      rw [hi]
      cases k with
      | inl c =>
          dsimp only [oldCellIncl, Sum.map_inl, id]
          rw [show (restrictedStructuralMap core hcore extra p).cells
              (Finsupp.single (Sum.inl c) a) = _ from
            finiteSpineFamilyStructuralMap_core_cell _ _ _
              (restrictedPresentation_surface core hcore extra p) c a]
          rw [show (blockInclusion core hcore extra hpt).cells (Finsupp.single (Sum.inl c) _) =
              Finsupp.single (Sum.inl c) _ from
            PresInclusionFS.cells_single _ _ _ _ _ _ _]
          rw [show (restrictedStructuralMap core hcore extra t).cells
              (Finsupp.single (Sum.inl c) _) = _ from
            finiteSpineFamilyStructuralMap_core_cell _ _ _
              (restrictedPresentation_surface core hcore extra t) c _]
          exact congrArg (Finsupp.single (Sum.inl c)) (hcoeff a)
      | inr s =>
          dsimp only [oldCellIncl, Sum.map_inr]
          change (blockInclusion core hcore extra hpt).cells (fsCellsF _ _ _ _ _) =
            fsCellsF _ _ _ _ _
          rw [fsCellsF_single_extra, fsCellsF_single_extra, PresMorFS.cells_smul]
          change _ • (blockInclusion core hcore extra hpt).cells
            (Finsupp.mapDomain (fun m => Sum.inr ⟨s, m⟩) _) = _
          rw [blockInclusion_surface_chain, blockInclusion_filling]
          exact congrArg (fun a => a • _) (hcoeff a)

/-- Actual rule-3 replacement preserves every old zero inclusion. -/
theorem blockInclusion_preserves_zero
    (hzero : ∀ x, FSIsFoxCycle (restrictedPresentation core hcore extra p) x →
      (normalizedInclusion core hcore extra hpt).cells x = 0)
    {x} (hx : FSIsFoxCycle (restrictedBlockPresentation core hcore extra p) x) :
    (blockInclusion core hcore extra hpt).cells x = 0 :=
  fsCells_eq_zero_of_generates (restrictedStructuralMap core hcore extra p)
    (restrictedStructuralMap core hcore extra t)
    (normalizedInclusion core hcore extra hpt) (blockInclusion core hcore extra hpt)
    (blockInclusion_structural_chain_square core hcore extra hpt) hzero
    (restrictedStructuralMap_generates core hcore extra p) hx

end FiniteChains.RelativeNormalForm
