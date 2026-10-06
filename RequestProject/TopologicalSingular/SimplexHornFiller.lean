module

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
Adapted from Vilin97/homotopy-groups-lean, commit
c66523531ff172d7f41913d94e56921e790a1b47; isolated geometry for Lean 4.28.0.
-/
public import RequestProject.TopologicalSingular.SimplexHornRetraction
public import Mathlib.Topology.LocallyFinite

@[expose] public section


open scoped Topology

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular

variable {d : ℕ} {X : Type} [TopologicalSpace X]

/-- The closed region of the ambient simplex on which coordinate `j`, away from the missing
face `i`, realizes the least such coordinate. -/
def simplexHornFillRegion (i : Fin (d + 2)) (j : Fin (d + 1)) :
    Set (stdSimplex ℝ (Fin (d + 2))) :=
  {z | simplexHornMin i z = z.1 (i.succAbove j)}

theorem isClosed_simplexHornFillRegion (i : Fin (d + 2)) (j : Fin (d + 1)) :
    IsClosed (simplexHornFillRegion i j) := by
  apply isClosed_eq
  · exact continuous_simplexHornMin i
  · exact (continuous_apply (i.succAbove j)).comp continuous_subtype_val

/-- The minimum regions cover the entire ambient simplex. -/
theorem exists_mem_simplexHornFillRegion (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) :
    ∃ j : Fin (d + 1), z ∈ simplexHornFillRegion i j :=
  exists_simplexHornMin_eq i z

/-- On fill region `j`, the horn retraction lands on face `i.succAbove j`. -/
theorem simplexHornRetract_coord_eq_zero_of_mem_fillRegion
    (i : Fin (d + 2)) (j : Fin (d + 1))
    (z : stdSimplex ℝ (Fin (d + 2))) (hz : z ∈ simplexHornFillRegion i j) :
    (simplexHornRetract i z).1 (i.succAbove j) = 0 := by
  rw [simplexHornRetract_apply_coe, simplexHornRetractCoords_succAbove]
  exact sub_eq_zero.mpr hz.symm

/-- Coordinates on the remaining face obtained after applying the horn retraction. -/
def simplexHornFillFaceMap (i : Fin (d + 2)) (j : Fin (d + 1)) :
    C({z // z ∈ simplexHornFillRegion i j}, stdSimplex ℝ (Fin (d + 1))) where
  toFun z := dropMap (i.succAbove j)
    (simplexHornRetract_coord_eq_zero_of_mem_fillRegion i j z.1 z.2)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro k
    change Continuous fun z : {z // z ∈ simplexHornFillRegion i j} ↦
      (simplexHornRetract i z.1).1 ((i.succAbove j).succAbove k)
    exact ((continuous_apply ((i.succAbove j).succAbove k)).comp continuous_subtype_val).comp
      ((simplexHornRetract i).continuous.comp continuous_subtype_val)

/-- The local face coordinates reconstruct the horn retraction. -/
theorem faceMap_simplexHornFillFaceMap (i : Fin (d + 2)) (j : Fin (d + 1))
    (z : {z // z ∈ simplexHornFillRegion i j}) :
    faceMap (i.succAbove j) (simplexHornFillFaceMap i j z) = simplexHornRetract i z.1 :=
  faceMap_dropMap (i.succAbove j)
    (simplexHornRetract_coord_eq_zero_of_mem_fillRegion i j z.1 z.2)

/-- A canonical index of a minimum region containing an ambient simplex point. -/
def simplexHornFillIdx (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) : Fin (d + 1) :=
  (exists_mem_simplexHornFillRegion i z).choose

theorem simplexHornFillIdx_spec (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 2))) :
    z ∈ simplexHornFillRegion i (simplexHornFillIdx i z) :=
  (exists_mem_simplexHornFillRegion i z).choose_spec

/-- The pointwise horn filler obtained by selecting a minimum-coordinate face. -/
def simplexHornFillFun (i : Fin (d + 2))
    (g : Fin (d + 1) → C(stdSimplex ℝ (Fin (d + 1)), X))
    (z : stdSimplex ℝ (Fin (d + 2))) : X :=
  g (simplexHornFillIdx i z)
    (simplexHornFillFaceMap i (simplexHornFillIdx i z)
      ⟨z, simplexHornFillIdx_spec i z⟩)

/-- Compatibility of maps prescribed on all faces other than `i`. -/
def SimplexHornFaceCompatible (i : Fin (d + 2))
    (g : Fin (d + 1) → C(stdSimplex ℝ (Fin (d + 1)), X)) : Prop :=
  ∀ (j k : Fin (d + 1)) (y z : stdSimplex ℝ (Fin (d + 1))),
    faceMap (i.succAbove j) y = faceMap (i.succAbove k) z → g j y = g k z

/-- The selected-index definition of the filler agrees with any minimum region containing the
point. -/
theorem simplexHornFillFun_eq (i : Fin (d + 2))
    (g : Fin (d + 1) → C(stdSimplex ℝ (Fin (d + 1)), X))
    (hg : SimplexHornFaceCompatible i g) (z : stdSimplex ℝ (Fin (d + 2)))
    (j : Fin (d + 1)) (hj : z ∈ simplexHornFillRegion i j) :
    simplexHornFillFun i g z = g j (simplexHornFillFaceMap i j ⟨z, hj⟩) := by
  apply hg
  rw [faceMap_simplexHornFillFaceMap, faceMap_simplexHornFillFaceMap]

/-- Compatible maps on the faces of a topological horn extend continuously over the full
simplex. -/
def simplexHornFiller (i : Fin (d + 2))
    (g : Fin (d + 1) → C(stdSimplex ℝ (Fin (d + 1)), X))
    (hg : SimplexHornFaceCompatible i g) :
    C(stdSimplex ℝ (Fin (d + 2)), X) where
  toFun := simplexHornFillFun i g
  continuous_toFun := by
    let S : Fin (d + 1) → Set (stdSimplex ℝ (Fin (d + 2))) :=
      fun j ↦ simplexHornFillRegion i j
    refine (locallyFinite_of_finite S).continuous ?_ (fun j ↦ ?_) (fun j ↦ ?_)
    · refine Set.eq_univ_of_forall fun z ↦ ?_
      obtain ⟨j, hj⟩ := exists_mem_simplexHornFillRegion i z
      exact Set.mem_iUnion.2 ⟨j, hj⟩
    · exact isClosed_simplexHornFillRegion i j
    · rw [continuousOn_iff_continuous_restrict]
      have heq : (S j).domRestrict (simplexHornFillFun i g) =
          fun z : S j ↦ g j (simplexHornFillFaceMap i j z) := by
        funext z
        exact simplexHornFillFun_eq i g hg z.1 j z.2
      rw [heq]
      exact (g j).continuous.comp (simplexHornFillFaceMap i j).continuous

/-- On every prescribed face, the topological horn filler recovers the given map. -/
theorem simplexHornFiller_face (i : Fin (d + 2))
    (g : Fin (d + 1) → C(stdSimplex ℝ (Fin (d + 1)), X))
    (hg : SimplexHornFaceCompatible i g) (j : Fin (d + 1))
    (y : stdSimplex ℝ (Fin (d + 1))) :
    simplexHornFiller i g hg (faceMap (i.succAbove j) y) = g j y := by
  have hmem : faceMap (i.succAbove j) y ∈ simplexHorn i :=
    ⟨j, faceMap_coe_same (i.succAbove j) y⟩
  have hregion : faceMap (i.succAbove j) y ∈ simplexHornFillRegion i j := by
    change simplexHornMin i (faceMap (i.succAbove j) y) =
      (faceMap (i.succAbove j) y).1 (i.succAbove j)
    rw [simplexHornMin_eq_zero_of_mem i hmem, faceMap_coe_same]
  rw [show simplexHornFiller i g hg (faceMap (i.succAbove j) y) =
      simplexHornFillFun i g (faceMap (i.succAbove j) y) from rfl,
    simplexHornFillFun_eq i g hg _ j hregion]
  apply congrArg (g j)
  apply faceMap_injective (i.succAbove j)
  rw [faceMap_simplexHornFillFaceMap,
    simplexHornRetract_eq_self_of_mem i hmem]


end FiniteChains.TopologicalSingular
