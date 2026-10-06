module

public import RequestProject.GenerationStepFinsupp
public import RequestProject.BlockFamilyBlockwiseFinsupp
public import RequestProject.LemmaTerminal

@[expose] public section

/-! The terminal inclusion and the Cockcroft/trivial-group vanishing argument
for arbitrary presentations.  Only chains, not cell sets, are finite.
Pending Lean verification. -/

noncomputable section
open scoped Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open BlockFamily

variable {A B J L I : Type} [DecidableEq A] [DecidableEq B]

theorem PresMorFS.cells_finset_sum {ρ : J → FreeGroup A} {τ : L → FreeGroup B}
    (f : PresMorFS ρ τ) (s : Finset I)
    (v : I → J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    f.cells (∑ i ∈ s, v i) = ∑ i ∈ s, f.cells (v i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, f.cells_add, ih, Finset.sum_insert ha]

theorem fsCells_eq_zero_of_hom_trivial {ρ : J → FreeGroup A} {τ : L → FreeGroup B}
    (f : PresMorFS ρ τ) (htriv : ∀ g, f.hom g = 1)
    (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ))
    (hv : ∀ j, augPres ρ (v j) = 0) : f.cells v = 0 := by
  have hdec : v = ∑ j ∈ v.support, Finsupp.single j (v j) := (Finsupp.sum_single v).symm
  have hsingle (j : J) :
      Finsupp.single j (v j) = v j • Finsupp.single j (1 : MonoidAlgebra ℤ (PresGroup ρ)) := by
    ext k : 1
    by_cases h : j = k
    · subst k
      simp
    · simp [Ne.symm h]
  rw [hdec, f.cells_finset_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [hsingle, f.cells_smul, mapDomainRingHom_eq_single_augPres f.hom htriv, hv j]
  simp

theorem fsCells_eq_zero_of_isCockcroft_of_hom_trivial
    {ρ : J → FreeGroup A} {τ : L → FreeGroup B}
    (f : PresMorFS ρ τ) (hρ : FSIsCockcroft ρ) (htriv : ∀ g, f.hom g = 1)
    (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) (hv : FSIsFoxCycle ρ v) : f.cells v = 0 :=
  fsCells_eq_zero_of_hom_trivial f htriv v (hρ v hv)

variable (ρ : J → FreeGroup A) (ν : L → FreeGroup A)

def addRelsCellsFS (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    (J ⊕ L) →₀ MonoidAlgebra ℤ (PresGroup (addRels ρ ν)) :=
  Finsupp.mapDomain Sum.inl (v.mapRange (addRelsRingHom ρ ν) (map_zero _))

omit [DecidableEq A] in
@[simp] theorem addRelsCellsFS_inl (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) (j : J) :
    addRelsCellsFS ρ ν v (Sum.inl j) = addRelsRingHom ρ ν (v j) := by
  simp only [addRelsCellsFS, Finsupp.mapDomain_apply_of_injective Sum.inl_injective, Finsupp.mapRange_apply]

omit [DecidableEq A] in
@[simp] theorem addRelsCellsFS_inr (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) (l : L) :
    addRelsCellsFS ρ ν v (Sum.inr l) = 0 := by
  apply Finsupp.mapDomain_notin_range
  rintro ⟨j, h⟩
  exact Sum.inl_ne_inr h

omit [DecidableEq A] in
@[simp] theorem addRelsCellsFS_single (j : J) (a : MonoidAlgebra ℤ (PresGroup ρ)) :
    addRelsCellsFS ρ ν (Finsupp.single j a) =
      Finsupp.single (Sum.inl j) (addRelsRingHom ρ ν a) := by
  simp only [addRelsCellsFS, Finsupp.mapRange_single, Finsupp.mapDomain_single]

omit [DecidableEq A] in
theorem addRelsCellsFS_add (v w : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    addRelsCellsFS ρ ν (v + w) = addRelsCellsFS ρ ν v + addRelsCellsFS ρ ν w := by
  ext j : 1
  cases j <;> simp [map_add]

theorem addRelsCellsFS_boundary (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) (a : A) :
    coverSecondBoundary (relSub (addRels ρ ν)) (addRels ρ ν) (addRelsCellsFS ρ ν v) a =
      addRelsRingHom ρ ν (coverSecondBoundary (relSub ρ) ρ v a) := by
  induction v using Finsupp.induction_linear with
  | zero => simp [addRelsCellsFS]
  | add v w hv hw => simp only [addRelsCellsFS_add, map_add, Finsupp.add_apply, hv, hw]
  | single j c =>
      simp only [addRelsCellsFS_single, fsCoverSecondBoundary_apply,
        Finsupp.sum_single_index, zero_mul, foxMatrix_addRels_inl, map_mul]

def addRelsMorFS : PresMorFS ρ (addRels ρ ν) where
  hom := addRelsHom ρ ν
  cells := addRelsCellsFS ρ ν
  cells_add := addRelsCellsFS_add ρ ν
  cells_smul := by
    intro a v
    ext j : 1
    cases j <;>
      simp [Finsupp.smul_apply, smul_eq_mul, map_mul, addRelsRingHom]
  cells_cycle := by
    intro v hv
    change coverSecondBoundary _ _ v = 0 at hv
    ext a : 1
    rw [addRelsCellsFS_boundary, hv, Finsupp.zero_apply, map_zero]
    rfl
  cells_aug := by
    intro v hv j
    cases j with
    | inl j => rw [addRelsCellsFS_inl, augPres_addRelsRingHom, hv]
    | inr l => rw [addRelsCellsFS_inr, map_zero]

end FiniteChains
