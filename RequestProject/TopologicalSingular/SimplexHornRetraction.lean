module

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
Adapted from Vilin97/homotopy-groups-lean, commit
c66523531ff172d7f41913d94e56921e790a1b47; isolated geometry for Lean 4.28.0.
-/
public import RequestProject.TopologicalSingular.SimplexFaceCoordinates

@[expose] public section

/-!
# Retraction of a simplex onto a horn

For a chosen face `i` of a simplex, subtract the least barycentric coordinate away from `i`
from every coordinate away from `i`, and transfer the removed mass to coordinate `i`.  The
result lies in the horn obtained by deleting face `i`: at least one of the other coordinates is
zero.  This gives an explicit continuous retraction of the simplex onto that horn.

The straight-line homotopy to this retraction fixes the horn pointwise.  In particular, on the
missing face it fixes the whole boundary.  This is the geometric reduction used to replace one
face of a normalized simplex boundary by its attaching map through all the other faces.
-/

open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace FiniteChains.TopologicalSingular

variable {d : ℕ}

/-- The least barycentric coordinate away from `i`. -/
def simplexHornMin (i : Fin (d + 2)) (z : stdSimplex ℝ (Fin (d + 2))) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun j : Fin (d + 1) ↦ z.1 (i.succAbove j)

theorem simplexHornMin_nonneg (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) : 0 ≤ simplexHornMin i z := by
  apply Finset.le_inf' Finset.univ_nonempty
  intro j hj
  exact z.2.1 _

theorem simplexHornMin_le (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) (j : Fin (d + 1)) :
    simplexHornMin i z ≤ z.1 (i.succAbove j) :=
  Finset.inf'_le _ (Finset.mem_univ j)

theorem exists_simplexHornMin_eq (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) :
    ∃ j : Fin (d + 1), simplexHornMin i z = z.1 (i.succAbove j) := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ : Finset (Fin (d + 1)))) Finset.univ_nonempty
    (fun j ↦ z.1 (i.succAbove j))
  exact ⟨j, hj⟩

/-- The least coordinate away from the chosen face varies continuously. -/
theorem continuous_simplexHornMin (i : Fin (d + 2)) :
    Continuous (simplexHornMin i) :=
  Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun j _ ↦ (continuous_apply (i.succAbove j)).comp continuous_subtype_val)

/-- Barycentric coordinates of the retraction onto the horn opposite face `i`. -/
def simplexHornRetractCoords (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) : Fin (d + 2) → ℝ :=
  i.insertNth (z.1 i + (d + 1 : ℝ) * simplexHornMin i z)
    (fun j ↦ z.1 (i.succAbove j) - simplexHornMin i z)

@[simp]
theorem simplexHornRetractCoords_same (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) :
    simplexHornRetractCoords i z i = z.1 i + (d + 1 : ℝ) * simplexHornMin i z := by
  simp [simplexHornRetractCoords]

@[simp]
theorem simplexHornRetractCoords_succAbove (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) (j : Fin (d + 1)) :
    simplexHornRetractCoords i z (i.succAbove j) =
      z.1 (i.succAbove j) - simplexHornMin i z := by
  simp [simplexHornRetractCoords]

theorem simplexHornRetractCoords_nonneg (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) (k : Fin (d + 2)) :
    0 ≤ simplexHornRetractCoords i z k := by
  refine Fin.succAboveCases i ?_ (fun j ↦ ?_) k
  · rw [simplexHornRetractCoords_same]
    have hd : (0 : ℝ) ≤ (d : ℝ) + 1 := by positivity
    exact add_nonneg (z.2.1 i)
      (mul_nonneg hd (simplexHornMin_nonneg i z))
  · rw [simplexHornRetractCoords_succAbove]
    exact sub_nonneg.mpr (simplexHornMin_le i z j)

theorem sum_simplexHornRetractCoords (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) :
    ∑ k, simplexHornRetractCoords i z k = 1 := by
  rw [Fin.sum_univ_succAbove _ i]
  simp only [simplexHornRetractCoords_same, simplexHornRetractCoords_succAbove,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hz := z.2.2
  rw [Fin.sum_univ_succAbove _ i] at hz
  norm_num at hz ⊢
  linarith

/-- The explicit retraction of a simplex onto the horn obtained by deleting face `i`. -/
def simplexHornRetract (i : Fin (d + 2)) :
    C(stdSimplex ℝ (Fin (d + 2)), stdSimplex ℝ (Fin (d + 2))) where
  toFun z := ⟨simplexHornRetractCoords i z,
    simplexHornRetractCoords_nonneg i z, sum_simplexHornRetractCoords i z⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro k
    refine Fin.succAboveCases i ?_ (fun j ↦ ?_) k
    · simp only [simplexHornRetractCoords_same]
      apply Continuous.add
      · exact (continuous_apply i).comp continuous_subtype_val
      · exact continuous_const.mul (continuous_simplexHornMin i)
    · simp only [simplexHornRetractCoords_succAbove]
      exact ((continuous_apply (i.succAbove j)).comp continuous_subtype_val).sub
        (continuous_simplexHornMin i)

@[simp]
theorem simplexHornRetract_apply_coe (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) (k : Fin (d + 2)) :
    (simplexHornRetract i z).1 k = simplexHornRetractCoords i z k :=
  rfl

/-- The horn opposite `i`, described as the points having a zero coordinate away from `i`. -/
def simplexHorn (i : Fin (d + 2)) : Set (stdSimplex ℝ (Fin (d + 2))) :=
  {z | ∃ j : Fin (d + 1), z.1 (i.succAbove j) = 0}

theorem simplexHornRetract_mem (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) : simplexHornRetract i z ∈ simplexHorn i := by
  obtain ⟨j, hj⟩ := exists_simplexHornMin_eq i z
  refine ⟨j, ?_⟩
  rw [simplexHornRetract_apply_coe, simplexHornRetractCoords_succAbove, hj, sub_self]

theorem simplexHornMin_eq_zero_of_mem (i : Fin (d + 2))
    {z : stdSimplex ℝ (Fin (d + 2))} (hz : z ∈ simplexHorn i) :
    simplexHornMin i z = 0 := by
  obtain ⟨j, hj⟩ := hz
  apply le_antisymm
  · simpa [hj] using simplexHornMin_le i z j
  · exact simplexHornMin_nonneg i z

theorem simplexHornRetract_eq_self_of_mem (i : Fin (d + 2))
    {z : stdSimplex ℝ (Fin (d + 2))} (hz : z ∈ simplexHorn i) :
    simplexHornRetract i z = z := by
  apply Subtype.ext
  funext k
  refine Fin.succAboveCases i ?_ (fun j ↦ ?_) k
  · simp [simplexHornRetractCoords, simplexHornMin_eq_zero_of_mem i hz]
  · simp [simplexHornRetractCoords, simplexHornMin_eq_zero_of_mem i hz]


end FiniteChains.TopologicalSingular
