import RequestProject.QCubeThreeOrientationSubdivision
import RequestProject.QCubeThreeBaseCycles

/-! Recovery of the actual cubical boundary of an isolated strict three-cube component. -/
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qCube_three_component_boundary_scalar (c : QCube A) (u v w : V)
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w})
    (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2) :
    ∃ k : ℤ, strictOrdBoundary3 (y.filter (fun t => t.1.2.2.2 = c)) =
      k • cubeThreeSquareBoundary c u v w (Ne.symm huv.ne)
        (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs := by
  obtain ⟨r, hcycle, hsupport, he⟩ := qCube_three_component_facet_boundary c
    (qCube_three_card c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
      (Ne.symm hvw.ne) hs) y hy hb
  have hr : ∀ s ∈ r.support, s.1 < c := by
    intro s hmem
    obtain ⟨a, ha, h0 | h1⟩ := hsupport s hmem
    · rw [h0]
      exact qCubeFacet_lt c a 0 ha
    · rw [h1]
      exact qCubeFacet_lt c a 1 ha
  obtain ⟨k, hk⟩ := qThreeFacetCycle_subdivision c u v w huv hvw hs r hr
    ((qSquareCubicalBoundary_zero_iff r).mpr hcycle)
  refine ⟨-k, ?_⟩
  have hn := congrArg Neg.neg (he.symm.trans hk)
  simpa only [neg_neg, neg_smul] using hn

end FiniteChains.Davis
