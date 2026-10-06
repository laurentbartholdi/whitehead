module

public import RequestProject.QCubeCanonicalTwoCycles
public import RequestProject.QCubeSquareCoefficientSigns

@[expose] public section

/-! A two-cycle avoiding the positive origin has no positive-square coefficients. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qSquare_positive_flag_origin (c : QSquare A) (hsgn : c.1.sgn = 0) :
    (squareFlag c.1 (qSquareLeft c) (qSquareRight c) (qSquare_directions_ne c)
      (qSquare_free_directions c) (false, 0, true)).1.1.spx = ∅ ∧
    (squareFlag c.1 (qSquareLeft c) (qSquareRight c) (qSquare_directions_ne c)
      (qSquare_free_directions c) (false, 0, true)).1.1.sgn = 0 := by
  constructor
  · rfl
  · funext x
    simp [squareFlag, squareEndpointFlag, squarePositiveFlag, cubePositiveVertex,
      qCubeFacet, hsgn]

/-- Actual positive-square coefficients vanish for every dimension-two cycle whose
coefficients at flags through the removed positive origin vanish. -/
theorem qSquareCycleCoefficients_positive_zero
    (z : (strictOrderCx (QCube A)).F →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2.2.spx.card ≤ 2)
    (hcycle : Comb.bdry2 (strictOrderCx (QCube A)) z = 0)
    (horigin : ∀ t : (strictOrderCx (QCube A)).F,
      t.1.1.spx = ∅ ∧ t.1.1.sgn = 0 → z t = 0)
    (c : QSquare A) (hsgn : c.1.sgn = 0) : qSquareCycleCoefficients z c = 0 := by
  classical
  let t := squareFlag c.1 (qSquareLeft c) (qSquareRight c) (qSquare_directions_ne c)
    (qSquare_free_directions c) (false, 0, true)
  have ht := horigin t (qSquare_positive_flag_origin c hsgn)
  have he := congrArg (fun r => r t)
    (cubeTwoCycle_square_component c.1 (qSquareLeft c) (qSquareRight c)
      (qSquare_directions_ne c) (qSquare_free_directions c) z hz hcycle)
  simp only [t, Finsupp.filter_apply, squareFlag_top, Finsupp.smul_apply,
    squareSubdivision_flag_coefficient] at he
  rw [ht] at he
  norm_num [squareFlagSign, smul_eq_mul] at he
  exact he

end FiniteChains.Davis
