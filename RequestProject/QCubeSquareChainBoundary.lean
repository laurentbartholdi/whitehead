module

public import RequestProject.QCubeSquareChainEmbedding

@[expose] public section

/-! Degree-two boundary naturality of the actual finite square-chain subdivision. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V C : Type} [DecidableEq V] {A : CommRel V}
  (cell : C → QCube A) (left right : C → V)
  (hne : ∀ i, left i ≠ right i) (hspx : ∀ i, (cell i).spx = {left i, right i})

noncomputable def squareChainEdgeBoundary : (C →₀ ℤ) →ₗ[ℤ]
    ((strictOrderCx (QCube A)).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ
    (fun i => cubeSquareEdgeBoundary (cell i) (left i) (right i) (hne i) (hspx i))

theorem squareChainSubdivision_boundary (z : C →₀ ℤ) :
    Comb.bdry2 (strictOrderCx (QCube A))
      (squareChainSubdivision cell left right hne hspx z) =
      squareChainEdgeBoundary cell left right hne hspx z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add]
  | single i n =>
      rw [squareChainSubdivision, Finsupp.linearCombination_single, map_smul,
        cubeSquareSubdivision_boundary, squareChainEdgeBoundary,
        Finsupp.linearCombination_single]

theorem squareChainEdgeBoundary_cycle (z : C →₀ ℤ) :
    Comb.bdry1 (strictOrderCx (QCube A))
      (squareChainEdgeBoundary cell left right hne hspx z) = 0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => rw [map_add, map_add, hz, hw, add_zero]
  | single i n =>
      rw [squareChainEdgeBoundary, Finsupp.linearCombination_single, map_smul,
        cubeSquareEdgeBoundary_cycle, smul_zero]

/-- Genuine square cycles correspond exactly to cycles of their strict subdivision. -/
theorem squareChainSubdivision_cycle_iff (z : C →₀ ℤ) :
    Comb.bdry2 (strictOrderCx (QCube A))
      (squareChainSubdivision cell left right hne hspx z) = 0 ↔
      squareChainEdgeBoundary cell left right hne hspx z = 0 := by
  rw [squareChainSubdivision_boundary]

end FiniteChains.Davis
