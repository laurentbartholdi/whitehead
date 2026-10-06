module

public import RequestProject.QCubeCoordinateThreeChains
public import RequestProject.QCubePositiveSquareCoefficients

@[expose] public section

/-! Ordinary positive boundary coefficients detect the simplicial cut cycle. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [Fintype V] {A : CommRel V}

/-- Coordinate transport preserves vanishing of all positive square coefficients. -/
theorem qSquareCoordinate_positive_zero (r : QSquare A →₀ ℤ)
    (hr : ∀ c : QSquare A, c.1.sgn = 0 → r c = 0) (σ : Finset V) :
    Finsupp.lmapDomain ℤ ℤ (fun c : QSquare A => qCubeToCoordinate c.1) r (posCube σ) = 0 := by
  classical
  let f : QSquare A → Cube V := fun c => qCubeToCoordinate c.1
  have hinj : Function.Injective f := by
    intro c d he
    exact Subtype.ext (qCubeToCoordinate_injective he)
  change Finsupp.mapDomain f r (posCube σ) = 0
  by_cases hσ : posCube σ ∈ Set.range f
  · obtain ⟨c, hc⟩ := hσ
    rw [← hc, Finsupp.mapDomain_apply_of_injective hinj]
    exact hr c ((qCube_coordinate_pos_iff c.1 σ).mp hc.symm).2
  · exact Finsupp.mapDomain_notin_range _ _ hσ

end FiniteChains.Davis
