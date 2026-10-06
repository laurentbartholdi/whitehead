module

public import RequestProject.QCubeTwoCycleSubdivision

@[expose] public section

/-! The actual square cells and their unconditional finite two-cycle subdivision dictionary. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

abbrev QSquare (A : CommRel V) := {c : QCube A // c.spx.card = 2}

noncomputable def qSquareFrame (c : QSquare A) :
    {p : V × V // p.2 < p.1 ∧ c.1.spx = {p.1, p.2}} := by
  apply Classical.choice
  obtain ⟨a, b, hne, hs⟩ := Finset.card_eq_two.mp c.2
  rcases lt_or_gt_of_ne hne with hab | hba
  · exact ⟨⟨(b, a), hab, by simpa [Finset.pair_comm] using hs⟩⟩
  · exact ⟨⟨(a, b), hba, hs⟩⟩

noncomputable def qSquareLeft (c : QSquare A) : V := (qSquareFrame c).1.1
noncomputable def qSquareRight (c : QSquare A) : V := (qSquareFrame c).1.2

theorem qSquare_directions_ne (c : QSquare A) : qSquareLeft c ≠ qSquareRight c :=
  Ne.symm (qSquareFrame c).2.1.ne

theorem qSquare_directions_decreasing (c : QSquare A) : qSquareRight c < qSquareLeft c :=
  (qSquareFrame c).2.1

theorem qSquare_free_directions (c : QSquare A) : c.1.spx = {qSquareLeft c, qSquareRight c} :=
  (qSquareFrame c).2.2

noncomputable def qSquareChainSubdivision : (QSquare A →₀ ℤ) →ₗ[ℤ]
    ((strictOrderCx (QCube A)).F →₀ ℤ) :=
  squareChainSubdivision Subtype.val qSquareLeft qSquareRight
    qSquare_directions_ne qSquare_free_directions

noncomputable def qSquareCycleCoefficients : ((strictOrderCx (QCube A)).F →₀ ℤ) →ₗ[ℤ]
    (QSquare A →₀ ℤ) :=
  squareCycleCoefficients Subtype.val qSquareLeft qSquareRight
    qSquare_directions_ne qSquare_free_directions Subtype.val_injective

noncomputable def qSquareFacetBoundary : (QSquare A →₀ ℤ) →ₗ[ℤ]
    ((strictOrderCx (QCube A)).E →₀ ℤ) :=
  squareChainEdgeBoundary Subtype.val qSquareLeft qSquareRight
    qSquare_directions_ne qSquare_free_directions

theorem qSquareChainSubdivision_injective : Function.Injective
    (qSquareChainSubdivision (A := A)) :=
  squareChainSubdivision_injective _ _ _ _ _ Subtype.val_injective

/-- Every actual strict two-cycle supported in cube dimension at most two is exactly the
subdivision of its finite integer chain on the actual square cells. -/
theorem qCube_twoCycle_reconstruction (z : (strictOrderCx (QCube A)).F →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2.2.spx.card ≤ 2)
    (hcycle : Comb.bdry2 (strictOrderCx (QCube A)) z = 0) :
    qSquareChainSubdivision (qSquareCycleCoefficients z) = z :=
  (cubeTwoCycle_is_squareSubdivision Subtype.val qSquareLeft qSquareRight
    qSquare_directions_ne qSquare_free_directions Subtype.val_injective
    (fun c hc => ⟨⟨c, hc⟩, rfl⟩) z hz hcycle).symm

theorem qCube_twoCycle_coefficients_cycle (z : (strictOrderCx (QCube A)).F →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2.2.spx.card ≤ 2)
    (hcycle : Comb.bdry2 (strictOrderCx (QCube A)) z = 0) :
    qSquareFacetBoundary (qSquareCycleCoefficients z) = 0 :=
  cubeTwoCycle_coefficients_cycle Subtype.val qSquareLeft qSquareRight
    qSquare_directions_ne qSquare_free_directions Subtype.val_injective
    (fun c hc => ⟨⟨c, hc⟩, rfl⟩) z hz hcycle

/-- Recovering coefficients is a left inverse on all finite chains of actual square cells. -/
theorem qSquare_coefficients_subdivision (r : QSquare A →₀ ℤ) :
    qSquareCycleCoefficients (qSquareChainSubdivision r) = r := by
  classical
  ext c
  change qSquareChainSubdivision r
    (squareFlag c.1 (qSquareLeft c) (qSquareRight c) (qSquare_directions_ne c)
      (qSquare_free_directions c) (false, 0, false)) = r c
  have he := congrArg (fun z : (strictOrderCx (QCube A)).F →₀ ℤ =>
      z (squareFlag c.1 (qSquareLeft c) (qSquareRight c) (qSquare_directions_ne c)
        (qSquare_free_directions c) (false, 0, false)))
    (squareChainSubdivision_filter_top Subtype.val qSquareLeft qSquareRight
      qSquare_directions_ne qSquare_free_directions Subtype.val_injective r c)
  have hc := squareSubdivision_flag_coefficient c.1 (qSquareLeft c) (qSquareRight c)
    (qSquare_directions_ne c) (qSquare_free_directions c) (false, 0, false)
  simp only [squareFlagSign] at hc
  norm_num at hc
  simpa only [if_true, qSquareChainSubdivision, Finsupp.filter_apply, squareFlag_top, Finsupp.smul_apply, hc,
    smul_eq_mul, mul_one] using he

end FiniteChains.Davis
