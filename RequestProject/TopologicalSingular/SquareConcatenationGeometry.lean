module

public import RequestProject.TopologicalSingular.SquareSubdivisionGeometry

@[expose] public section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

theorem transAt_leftRectangle (p q : GenLoop (Fin 2) X x) :
    (GenLoop.transAt 0 p q).val.comp (leftRectangle squareHalf) = p.val := by
  apply ContinuousMap.ext
  intro z
  change (if ((leftRectangle squareHalf z) 0 : ℝ) ≤ 1 / 2
    then p (Function.update (leftRectangle squareHalf z) 0
      (Set.projIcc 0 1 zero_le_one (2 * (leftRectangle squareHalf z) 0)))
    else q (Function.update (leftRectangle squareHalf z) 0
      (Set.projIcc 0 1 zero_le_one (2 * (leftRectangle squareHalf z) 0 - 1)))) = p z
  have hh : ((leftRectangle squareHalf z) 0 : ℝ) ≤ 1 / 2 := by
    change (1 / 2 : ℝ) * (z 0 : ℝ) ≤ 1 / 2
    nlinarith [(z 0).property.2]
  rw [if_pos hh]
  apply congrArg p
  funext i
  fin_cases i
  · simp only [Function.update_apply]
    rw [if_pos (by rfl)]
    have he : 2 * ((leftRectangle squareHalf z) 0 : ℝ) = (z 0 : ℝ) := by
      change 2 * ((1 / 2 : ℝ) * (z 0 : ℝ)) = _
      ring
    rw [he, Set.projIcc_of_mem zero_le_one (z 0).property]
    exact Subtype.ext rfl
  · simp [leftRectangle]

theorem rightRectangle_half_coordinate (z : Fin 2 → I) :
    ((rightRectangle squareHalf z) 0 : ℝ) = (1 + (z 0 : ℝ)) / 2 := by
  change 1 - ((1 - (1 / 2 : ℝ)) * (1 - (z 0 : ℝ))) = _
  ring

theorem transAt_rightRectangle (p q : GenLoop (Fin 2) X x) :
    (GenLoop.transAt 0 p q).val.comp (rightRectangle squareHalf) = q.val := by
  apply ContinuousMap.ext
  intro z
  change (if ((rightRectangle squareHalf z) 0 : ℝ) ≤ 1 / 2
    then p (Function.update (rightRectangle squareHalf z) 0
      (Set.projIcc 0 1 zero_le_one (2 * (rightRectangle squareHalf z) 0)))
    else q (Function.update (rightRectangle squareHalf z) 0
      (Set.projIcc 0 1 zero_le_one (2 * (rightRectangle squareHalf z) 0 - 1)))) = q z
  split_ifs with h
  · have hz : z 0 = 0 := by
      apply Subtype.ext
      have hr := rightRectangle_half_coordinate z
      change (z 0 : ℝ) = 0
      nlinarith [(z 0).property.1]
    have he : 2 * ((rightRectangle squareHalf z) 0 : ℝ) = 1 := by
      rw [rightRectangle_half_coordinate, hz]
      norm_num
    calc
      _ = x := GenLoop.boundary p _ ⟨0, Or.inr (by
        simp only [Function.update_self]
        rw [he]
        exact Set.projIcc_right _ )⟩
      _ = q z := (GenLoop.boundary q z ⟨0, Or.inl hz⟩).symm
  · apply congrArg q
    funext i
    fin_cases i
    · simp only [Function.update_apply]
      rw [if_pos (by rfl)]
      have he : 2 * ((rightRectangle squareHalf z) 0 : ℝ) - 1 = (z 0 : ℝ) := by
        rw [rightRectangle_half_coordinate]
        ring
      rw [he, Set.projIcc_of_mem zero_le_one (z 0).property]
      exact Subtype.ext rfl
    · simp [rightRectangle]

end FiniteChains.TopologicalSingular
