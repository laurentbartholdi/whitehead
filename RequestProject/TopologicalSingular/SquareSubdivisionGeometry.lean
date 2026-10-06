module

public import RequestProject.TopologicalSingular.SquareSingularHomotopy

@[expose] public section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology

noncomputable def squareHalf : I := ⟨1 / 2, by constructor <;> norm_num⟩

def leftRectangle (a : I) : C((Fin 2 → I), Fin 2 → I) where
  toFun z := ![a * z 0, z 1]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact (continuous_const.mul ((continuous_apply 0).subtype_val)).subtype_mk _
    · exact continuous_apply 1

def rightRectangle (a : I) : C((Fin 2 → I), Fin 2 → I) where
  toFun z := ![unitInterval.symm (unitInterval.symm a * unitInterval.symm (z 0)), z 1]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact unitInterval.continuous_symm.comp
        ((continuous_const.mul
          ((unitInterval.continuous_symm.comp (continuous_apply 0)).subtype_val)).subtype_mk _)
    · exact continuous_apply 1

noncomputable def leftRectangleSweep : ContinuousMap.Homotopy (leftRectangle 0) (leftRectangle squareHalf) where
  toFun w := leftRectangle (w.1 * squareHalf) w.2
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact ((continuous_fst.subtype_val.mul continuous_const).mul
        (((continuous_apply 0).comp continuous_snd).subtype_val)).subtype_mk _
    · change Continuous (fun w : I × (Fin 2 → I) => w.2 1)
      exact (continuous_apply 1).comp continuous_snd
  map_zero_left z := by simp
  map_one_left z := by simp

noncomputable def rightRectangleSweep : ContinuousMap.Homotopy (rightRectangle 0) (rightRectangle squareHalf) where
  toFun w := rightRectangle (w.1 * squareHalf) w.2
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact unitInterval.continuous_symm.comp
        (((unitInterval.continuous_symm.comp
          ((continuous_fst.subtype_val.mul continuous_const).subtype_mk _)).subtype_val.mul
            ((unitInterval.continuous_symm.comp
              ((continuous_apply 0).comp continuous_snd)).subtype_val)).subtype_mk _)
    · change Continuous (fun w : I × (Fin 2 → I) => w.2 1)
      exact (continuous_apply 1).comp continuous_snd
  map_zero_left z := by simp
  map_one_left z := by simp

theorem rightRectangle_zero : rightRectangle 0 = ContinuousMap.id (Fin 2 → I) := by
  apply ContinuousMap.ext
  intro z
  funext i
  fin_cases i <;> simp [rightRectangle]

theorem rectangle_common_edge (a : I) (z : Domain 1) :
    leftRectangle a (cubeEdge 0 1 z) = rightRectangle a (cubeEdge 0 0 z) := by
  funext i
  fin_cases i <;> simp [leftRectangle, rightRectangle, cubeEdge, Whitehead.squareEdge]

theorem leftRectangle_horizontal_boundary (a v : I) (hv : v = 0 ∨ v = 1) (z : Domain 1) :
    leftRectangle a (cubeEdge 1 v z) ∈ Cube.boundary (Fin 2) := by
  refine ⟨1, ?_⟩
  simpa [leftRectangle, cubeEdge, Whitehead.squareEdge] using hv

theorem rightRectangle_horizontal_boundary (a v : I) (hv : v = 0 ∨ v = 1) (z : Domain 1) :
    rightRectangle a (cubeEdge 1 v z) ∈ Cube.boundary (Fin 2) := by
  refine ⟨1, ?_⟩
  simpa [rightRectangle, cubeEdge, Whitehead.squareEdge] using hv

theorem leftRectangle_outer_boundary (a : I) (z : Domain 1) :
    leftRectangle a (cubeEdge 0 0 z) ∈ Cube.boundary (Fin 2) := by
  exact ⟨0, Or.inl (by simp [leftRectangle, cubeEdge, Whitehead.squareEdge])⟩

theorem rightRectangle_outer_boundary (a : I) (z : Domain 1) :
    rightRectangle a (cubeEdge 0 1 z) ∈ Cube.boundary (Fin 2) := by
  exact ⟨0, Or.inr (by simp [rightRectangle, cubeEdge, Whitehead.squareEdge])⟩

theorem leftRectangle_zero_boundary (z : Fin 2 → I) :
    leftRectangle 0 z ∈ Cube.boundary (Fin 2) :=
  ⟨0, Or.inl (by simp [leftRectangle])⟩

end FiniteChains.TopologicalSingular
