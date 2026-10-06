module

public import RequestProject.CockcroftRelatorReindex
public import RequestProject.GenerationStepFinsupp
public import RequestProject.BlockFamilyBlockwiseFinsupp

@[expose] public section

/-! Relator reindexing for arbitrary presentations and finitely supported
chains. No finiteness of the generators or relators is imposed.
Pending Lean verification. -/

noncomputable section
open scoped Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.RelatorReindex
open BlockFamily

universe u
variable {A J K : Type u} [DecidableEq A]
  (ρ : J → FreeGroup A) (τ : K → FreeGroup A) (e : J ≃ K)
  (hrel : ∀ j, τ (e j) = ρ j)

def cellsFS (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    K →₀ MonoidAlgebra ℤ (PresGroup τ) :=
  Finsupp.mapDomain e (v.mapRange (coefficientMap ρ τ e hrel) (map_zero _))

omit [DecidableEq A] in
@[simp] theorem cellsFS_apply_image
    (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) (j : J) :
    cellsFS ρ τ e hrel v (e j) = coefficientMap ρ τ e hrel (v j) := by
  simp only [cellsFS, Finsupp.mapDomain_apply_of_injective e.injective, Finsupp.mapRange_apply]

omit [DecidableEq A] in
theorem cellsFS_apply (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) (k : K) :
    cellsFS ρ τ e hrel v k = coefficientMap ρ τ e hrel (v (e.symm k)) := by
  simpa only [Equiv.apply_symm_apply] using cellsFS_apply_image ρ τ e hrel v (e.symm k)

omit [DecidableEq A] in
@[simp] theorem cellsFS_single (j : J) (a : MonoidAlgebra ℤ (PresGroup ρ)) :
    cellsFS ρ τ e hrel (Finsupp.single j a) =
      Finsupp.single (e j) (coefficientMap ρ τ e hrel a) := by
  simp only [cellsFS, Finsupp.mapRange_single, Finsupp.mapDomain_single]

omit [DecidableEq A] in
theorem cellsFS_add (v w : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    cellsFS ρ τ e hrel (v + w) = cellsFS ρ τ e hrel v + cellsFS ρ τ e hrel w := by
  ext k : 1
  simp only [cellsFS_apply, Finsupp.add_apply, map_add]

theorem cellsFS_boundary_apply (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) (a : A) :
    coverSecondBoundary (relSub τ) τ (cellsFS ρ τ e hrel v) a =
      coefficientMap ρ τ e hrel (coverSecondBoundary (relSub ρ) ρ v a) := by
  induction v using Finsupp.induction_linear with
  | zero => simp [cellsFS]
  | add v w hv hw =>
      simp only [cellsFS_add, map_add, Finsupp.add_apply, hv, hw]
  | single j c =>
      simp only [cellsFS_single, fsCoverSecondBoundary_apply, Finsupp.sum_single_index,
        zero_mul, map_mul, coefficientMap_matrix]

theorem cellsFS_cycle (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ))
    (hv : FSIsFoxCycle ρ v) : FSIsFoxCycle τ (cellsFS ρ τ e hrel v) := by
  change coverSecondBoundary (relSub ρ) ρ v = 0 at hv
  apply Finsupp.ext
  intro a
  simp only [cellsFS_boundary_apply, hv, Finsupp.zero_apply, map_zero]

omit [DecidableEq A] in
theorem cellsFS_aug (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) (k : K) :
    augPres τ (cellsFS ρ τ e hrel v k) = augPres ρ (v (e.symm k)) := by
  rw [cellsFS_apply]
  exact augQ_mapDomain (groupMap ρ τ e hrel) (v (e.symm k))

def morFS : PresMorFS ρ τ where
  hom := groupMap ρ τ e hrel
  cells := cellsFS ρ τ e hrel
  cells_add := cellsFS_add ρ τ e hrel
  cells_smul := by
    intro a v
    ext k : 1
    simp only [cellsFS_apply, Finsupp.smul_apply, smul_eq_mul, map_mul, coefficientMap]
  cells_cycle := cellsFS_cycle ρ τ e hrel
  cells_aug := by
    intro v hv k
    rw [cellsFS_aug]
    exact hv (e.symm k)

include hrel in
theorem fsIsCockcroft_of (hτ : FSIsCockcroft τ) : FSIsCockcroft ρ := by
  intro v hv j
  have h := hτ (cellsFS ρ τ e hrel v) (cellsFS_cycle ρ τ e hrel v hv) (e j)
  simpa only [cellsFS_aug, Equiv.symm_apply_apply] using h

include hrel in
theorem fsIsCockcroft_iff : FSIsCockcroft ρ ↔ FSIsCockcroft τ := by
  constructor
  · intro hρ
    have hs : ∀ k, ρ (e.symm k) = τ k := by
      intro k
      simpa only [Equiv.apply_symm_apply] using (hrel (e.symm k)).symm
    exact fsIsCockcroft_of τ ρ e.symm hs hρ
  · exact fsIsCockcroft_of ρ τ e hrel

end FiniteChains.RelatorReindex
