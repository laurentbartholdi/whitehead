module

public import RequestProject.QCubeTruncatedCoordinateBoundary

@[expose] public section

/-! The actual finite truncated three-boundaries are killed by their geometric collapse. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [Fintype V] [LinearOrder V] {A : CommRel V}

theorem qThreeTruncatedCoordinateBoundary_apply (r : QThreeCube A →₀ ℤ)
    (f : Cube V ⊕ Finset V) :
    qThreeTruncatedCoordinateBoundary r f =
      ∑ c ∈ r.support, r c * cubeBdry (qCubeToCoordinate c.1) f := by
  classical
  simp only [qThreeTruncatedCoordinateBoundary, Finsupp.linearCombination_apply,
    Finsupp.sum, Finsupp.finset_sum_apply, Finsupp.smul_apply,
    qCubeTruncatedCoordinateBoundary_apply, smul_eq_mul]

/-- A geometric chain collapse kills every genuine finite truncated boundary whose
three-cubes occur in the actual collapse sequence. -/
theorem qThreeTruncatedBoundary_collapse_zero
    (lp : List (Cube V × (Cube V ⊕ Finset V)))
    (hlp : CollapseChain.IsChainCollapse (cubeBdry (V := V)) lp)
    (r : QThreeCube A →₀ ℤ)
    (hr : ∀ c ∈ r.support, ∃ f, (qCubeToCoordinate c.1, f) ∈ lp) :
    CollapseChain.cmap (cubeBdry (V := V)) lp
      (qThreeTruncatedCoordinateBoundary r) = 0 := by
  classical
  let L : ((Cube V ⊕ Finset V) → ℤ) →+ ((Cube V ⊕ Finset V) → ℤ) :=
    { toFun := CollapseChain.cmap (cubeBdry (V := V)) lp
      map_zero' := CollapseChain.cmap_zero lp
      map_add' := CollapseChain.cmap_add lp }
  have he : (qThreeTruncatedCoordinateBoundary r : (Cube V ⊕ Finset V) → ℤ) =
      ∑ c ∈ r.support, (fun f => r c * cubeBdry (qCubeToCoordinate c.1) f) := by
    funext f
    simp only [Finset.sum_apply, qThreeTruncatedCoordinateBoundary_apply]
  change L (qThreeTruncatedCoordinateBoundary r) = 0
  rw [he, map_sum]
  apply Finset.sum_eq_zero
  intro c hc
  obtain ⟨f, hf⟩ := hr c hc
  change CollapseChain.cmap (cubeBdry (V := V)) lp
    (fun g => r c * cubeBdry (qCubeToCoordinate c.1) g) = 0
  rw [CollapseChain.cmap_leftMul,
    CollapseChain.cmap_bdry_eq_zero hlp (qCubeToCoordinate c.1, f) hf]
  funext g
  simp

end FiniteChains.Davis
