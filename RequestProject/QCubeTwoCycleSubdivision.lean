module

public import RequestProject.QCubeSquareCycleRecovery
public import RequestProject.QCubeSquareChainBoundary

@[expose] public section

/-! Global recovery of actual two-dimensional strict cycles as finite cubical square chains. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V C : Type} [DecidableEq V] {A : CommRel V}
  (cell : C → QCube A) (left right : C → V)
  (hne : ∀ i, left i ≠ right i) (hspx : ∀ i, (cell i).spx = {left i, right i})

def squareCoefficientFlag (i : C) : (strictOrderCx (QCube A)).F :=
  squareFlag (cell i) (left i) (right i) (hne i) (hspx i) (false, 0, false)

theorem squareCoefficientFlag_injective (hcell : Function.Injective cell) :
    Function.Injective (squareCoefficientFlag cell left right hne hspx) := by
  intro i j h
  have ht := congrArg (fun t : (strictOrderCx (QCube A)).F => t.1.2.2) h
  simp only [squareCoefficientFlag, squareFlag_top] at ht
  exact hcell ht

noncomputable def squareCycleCoefficients (hcell : Function.Injective cell) :
    ((strictOrderCx (QCube A)).F →₀ ℤ) →ₗ[ℤ] (C →₀ ℤ) :=
  Finsupp.lcomapDomain (squareCoefficientFlag cell left right hne hspx)
    (squareCoefficientFlag_injective cell left right hne hspx hcell)

theorem squareChainSubdivision_off_cells (r : C →₀ ℤ)
    (t : (strictOrderCx (QCube A)).F) (ht : ∀ i, t.1.2.2 ≠ cell i) :
    squareChainSubdivision cell left right hne hspx r t = 0 := by
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s hr hs => simp only [map_add, Finsupp.add_apply, hr, hs, add_zero]
  | single i n =>
      rw [squareChainSubdivision, Finsupp.linearCombination_single, Finsupp.smul_apply,
        cubeSquareSubdivision_eq_zero_off_top _ _ _ _ _ _ (ht i), smul_zero]

/-- Every actual strict two-cycle of dimension at most two is the subdivision of its
finite recovered cubical coefficient chain. -/
theorem cubeTwoCycle_is_squareSubdivision (hcell : Function.Injective cell)
    (hcover : ∀ c : QCube A, c.spx.card = 2 → ∃ i, cell i = c)
    (z : (strictOrderCx (QCube A)).F →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2.2.spx.card ≤ 2)
    (hcycle : Comb.bdry2 (strictOrderCx (QCube A)) z = 0) :
    z = squareChainSubdivision cell left right hne hspx
      (squareCycleCoefficients cell left right hne hspx hcell z) := by
  classical
  ext t
  by_cases hdim : t.1.2.2.spx.card = 2
  · obtain ⟨i, hi⟩ := hcover t.1.2.2 hdim
    have hti : t.1.2.2 = cell i := hi.symm
    have hl := congrArg (fun w : (strictOrderCx (QCube A)).F →₀ ℤ => w t)
      (cubeTwoCycle_square_component (cell i) (left i) (right i) (hne i) (hspx i)
        z hz hcycle)
    have hr := congrArg (fun w : (strictOrderCx (QCube A)).F →₀ ℤ => w t)
      (squareChainSubdivision_filter_top cell left right hne hspx hcell
        (squareCycleCoefficients cell left right hne hspx hcell z) i)
    simp only [Finsupp.filter_apply, hti, Finsupp.smul_apply] at hl hr
    exact hl.trans hr.symm
  · have hzt : z t = 0 := by
      by_contra hzt
      exact hdim (qCube_triangle_dimensions t (hz t (Finsupp.mem_support_iff.mpr hzt))).2.2
    rw [hzt]
    symm
    apply squareChainSubdivision_off_cells
    intro i he
    apply hdim
    rw [he, hspx i]
    simp [hne i]

/-- The recovered cubical coefficients are genuine cycles for the facet boundary map. -/
theorem cubeTwoCycle_coefficients_cycle (hcell : Function.Injective cell)
    (hcover : ∀ c : QCube A, c.spx.card = 2 → ∃ i, cell i = c)
    (z : (strictOrderCx (QCube A)).F →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2.2.spx.card ≤ 2)
    (hcycle : Comb.bdry2 (strictOrderCx (QCube A)) z = 0) :
    squareChainEdgeBoundary cell left right hne hspx
      (squareCycleCoefficients cell left right hne hspx hcell z) = 0 := by
  rw [← squareChainSubdivision_boundary,
    ← cubeTwoCycle_is_squareSubdivision cell left right hne hspx hcell hcover z hz hcycle]
  exact hcycle

end FiniteChains.Davis
