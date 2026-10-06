module

public import RequestProject.GenerationStepFinsupp
public import RequestProject.GenusActualSpineB2

@[expose] public section

/-! The actual genus-block operation as a supported structural map.

B1, B2, and injectivity are discharged by the constructed genus blocks.
The retained cells are fixed literally. The resulting preservation theorems
are the rule-3 input to the fixed-core replacement induction.
No Lean verification has been run on this source yet.
-/

noncomputable section
open scoped Classical

namespace FiniteChains.BlockFamily

universe u

variable {α Jr S : Type u} {Z M : S → Type u}
  [DecidableEq α] [DecidableEq S] [∀ s, DecidableEq (Z s)]
  (ρ : Jr ⊕ S → FreeGroup α) (b : ∀ s, M s → FreeGroup (α ⊕ Z s))
  (hfill : FilledF ρ b)
  (c : ∀ s, M s →₀ MonoidAlgebra ℤ (PresGroup (substPresF ρ b)))

/-- The finite-support structural map of an arbitrary simultaneous block
replacement, with exactly the original coefficient map and surface fillings. -/
def substMorFS (hc : IsFillingFS ρ b hfill c) : PresMorFS ρ (substPresF ρ b) where
  hom := substHomF ρ b hfill
  cells := fsCellsF ρ b hfill c
  cells_add := by
    intro y z
    ext k : 1
    exact congrFun (cellsF_add ρ b hfill (fun s => c s) y z) k
  cells_smul := by
    intro a y
    ext k : 1
    exact congrFun (cellsF_smul ρ b hfill (fun s => c s) a y) k
  cells_cycle := by
    intro y hy
    change coverSecondBoundary _ _ (fsCellsF ρ b hfill c y) = 0
    rw [fsCellsF_boundary ρ b hfill c hc y, hy]
    simp
  cells_aug := by
    intro y hy k
    change augPres (substPresF ρ b) (cellsF ρ b hfill (fun s => c s) y k) = 0
    exact augPres_cellsF_eq_zero hy k

/-- The structural map preserves the retained two-cells exactly, including
their actual coefficients in the new group ring. -/
theorem substMorFS_retained (hc : IsFillingFS ρ b hfill c)
    (j : Jr) (a : MonoidAlgebra ℤ (PresGroup ρ)) :
    (substMorFS ρ b hfill c hc).cells (Finsupp.single (Sum.inl j) a) =
      Finsupp.single (Sum.inl j) (coeffF ρ b hfill a) := by
  ext k : 1
  cases k with
  | inl k =>
      change coeffF ρ b hfill (Finsupp.single (Sum.inl j) a (Sum.inl k)) = _
      by_cases h : k = j
      · subst k; simp
      · simp [h]
  | inr p =>
      change coeffF ρ b hfill (Finsupp.single (Sum.inl j) a (Sum.inr p.1)) *
        c p.1 p.2 = _
      simp

end FiniteChains.BlockFamily

namespace FiniteChains.Davis.Genus

open BlockFamily

variable {α Jr S : Type} (σ : Jr ⊕ S → FreeGroup α)
  (q : S → ℕ) [∀ s, NeZero (q s)]
  (u : ∀ s, Fin (q s) × Bool → FreeGroup α)
  (hσ : ∀ s, σ (Sum.inr s) = commWord (u s) (finitePairs (q s)))

/-- Rule 3 with all its geometric inputs supplied, including for an
infinite family over an infinite fixed core. -/
def finiteSpineFamilyStructuralMap :
    PresMorFS σ (substPresF σ (familyFiniteSpineWordBlock q u)) :=
  substMorFS σ (familyFiniteSpineWordBlock q u)
    (familyFiniteSpineWordBlock_filled σ q u hσ)
    (finiteSpineFamilyFilling σ q u)
    (finiteSpineFamilyFilling_isFilling σ q u hσ)

@[simp] theorem finiteSpineFamilyStructuralMap_cells
    (y : (Jr ⊕ S) →₀ MonoidAlgebra ℤ (PresGroup σ)) :
    (finiteSpineFamilyStructuralMap σ q u hσ).cells y =
      fsCellsF σ (familyFiniteSpineWordBlock q u)
        (familyFiniteSpineWordBlock_filled σ q u hσ)
        (finiteSpineFamilyFilling σ q u) y := rfl

/-- The group injection used in the fixed-core operation is the actual
substitution homomorphism, not an additional hypothesis. -/
theorem finiteSpineFamilyStructuralMap_injective :
    Function.Injective (finiteSpineFamilyStructuralMap σ q u hσ).hom :=
  familyFiniteSpineWordBlock_injective σ q u hσ

/-- Actual equation (3.3) for the simultaneous genus replacement. -/
theorem finiteSpineFamilyStructuralMap_generates :
    FSGenerates (finiteSpineFamilyStructuralMap σ q u hσ) := by
  intro y hy
  exact finiteSpineFamily_fsGenerates_actual σ q u hσ y hy

/-- The replacement retains every relator chosen as a core cell. -/
theorem finiteSpineFamilyStructuralMap_core_rel (j : Jr) :
    substPresF σ (familyFiniteSpineWordBlock q u) (Sum.inl j) =
      FreeGroup.map Sum.inl (σ (Sum.inl j)) := rfl

/-- On a retained core two-cell the structural map is literally the
labelled inclusion with its induced change of group-ring coefficients. -/
theorem finiteSpineFamilyStructuralMap_core_cell
    (j : Jr) (a : MonoidAlgebra ℤ (PresGroup σ)) :
    (finiteSpineFamilyStructuralMap σ q u hσ).cells
        (Finsupp.single (Sum.inl j) a) =
      Finsupp.single (Sum.inl j)
        (MonoidAlgebra.mapDomainRingHom ℤ
          (finiteSpineFamilyStructuralMap σ q u hσ).hom a) :=
  substMorFS_retained σ (familyFiniteSpineWordBlock q u)
    (familyFiniteSpineWordBlock_filled σ q u hσ)
    (finiteSpineFamilyFilling σ q u)
    (finiteSpineFamilyFilling_isFilling σ q u hσ) j a

include hσ in
/-- The actual genus replacement preserves Cockcroftness, without any
cardinality condition or a remaining B2 assumption. -/
theorem finiteSpineFamilyStructuralMap_cockcroft (hP : FSIsCockcroft σ) :
    FSIsCockcroft (substPresF σ (familyFiniteSpineWordBlock q u)) :=
  fsIsCockcroft_of_generates (finiteSpineFamilyStructuralMap σ q u hσ)
    (finiteSpineFamilyStructuralMap_generates σ q u hσ) hP

/-- Rule 3 preserves an old zero arrow through its actual commuting
structural square. The group/cell maps on that square may change the other
stage as well, as required by `(D,L₁,…,Lₘ) ↦ (D,TL₁,…,TLₘ,QLₘ)`. -/
theorem finiteSpineFamilyStructuralMap_preserves_zero
    {β K β' K' : Type} [DecidableEq β] [DecidableEq β']
    {τ : K → FreeGroup β} {τ' : K' → FreeGroup β'}
    (eta' : PresMorFS τ τ') (j : PresMorFS σ τ)
    (Tj : PresMorFS (substPresF σ (familyFiniteSpineWordBlock q u)) τ')
    (hsq : ∀ y, Tj.cells ((finiteSpineFamilyStructuralMap σ q u hσ).cells y) =
      eta'.cells (j.cells y))
    (hzero : ∀ y, FSIsFoxCycle σ y → j.cells y = 0)
    {z : (Jr ⊕ (Σ s, NamedSpineRel (q s))) →₀
      MonoidAlgebra ℤ (PresGroup (substPresF σ (familyFiniteSpineWordBlock q u)))}
    (hz : FSIsFoxCycle (substPresF σ (familyFiniteSpineWordBlock q u)) z) :
    Tj.cells z = 0 :=
  fsCells_eq_zero_of_generates (finiteSpineFamilyStructuralMap σ q u hσ)
    eta' j Tj hsq hzero (finiteSpineFamilyStructuralMap_generates σ q u hσ) hz

section Finite

variable [Fintype α] [Fintype Jr] [Fintype S]

/-- The actual rule-3 map in the original finite structural-map interface. -/
def finiteSpineFamilyPresMor :
    PresMor σ (substPresF σ (familyFiniteSpineWordBlock q u)) :=
  (finiteSpineFamilyStructuralMap σ q u hσ).toPresMor

omit [Fintype α] in
/-- B2 is now discharged in the precise interface used by `TPath` and
`lemma_terminal`; rules 1 and 2 can be composed with this map directly. -/
theorem finiteSpineFamilyPresMor_generates :
    Generates (finiteSpineFamilyPresMor σ q u hσ) :=
  (finiteSpineFamilyStructuralMap_generates σ q u hσ).toGenerates

include hσ in
omit [Fintype α] in
theorem finiteSpineFamilyPresMor_cockcroft (hP : IsCockcroft σ) :
    IsCockcroft (substPresF σ (familyFiniteSpineWordBlock q u)) :=
  isCockcroft_of_generates (finiteSpineFamilyPresMor σ q u hσ)
    (finiteSpineFamilyPresMor_generates σ q u hσ) hP

end Finite

end FiniteChains.Davis.Genus
