module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.SquareBoundaryNormHomeomorph

@[expose] public section

/-! Move both endpoints of a path along prescribed paths, extending the
motion continuously over the whole interval by the actual disk HEP. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open scoped Topology unitInterval Classical

variable {X : Type} [TopologicalSpace X]

structure IntervalEndpointExtension (f : C(I, X)) {x₀ x₁ : X}
    (p₀ : Path (f 0) x₀) (p₁ : Path (f 1) x₁) where
  map : C(I × I, X)
  zero : ∀ t, map (0, t) = f t
  side_zero : ∀ τ, map (τ, 0) = p₀ τ
  side_one : ∀ τ, map (τ, 1) = p₁ τ

def intervalEndpointExtension (f : C(I, X)) {x₀ x₁ : X}
    (p₀ : Path (f 0) x₀) (p₁ : Path (f 1) x₁) :
    IntervalEndpointExtension f p₀ p₁ := by
  let e := oneBallIntervalHomeomorph
  let P : C(UnitBoundary (Fin 1 → ℝ), C(I, X)) :=
    ⟨fun a => if a.val 0 = -1 then p₀.toContinuousMap else p₁.toContinuousMap,
      continuous_of_discreteTopology⟩
  have hP₀ : P (oneBoundaryPoint false) = p₀.toContinuousMap := by
    simp [P, oneBoundaryPoint]
  have hP₁ : P (oneBoundaryPoint true) = p₁.toContinuousMap := by
    norm_num [P, oneBoundaryPoint]
  let H : C(I × UnitBoundary (Fin 1 → ℝ), X) :=
    P.uncurry.comp ⟨Prod.swap, continuous_swap⟩
  let F := f.comp e.toContinuousMap
  have h₀ : ∀ a, H (0, a) = F (unitBoundaryInclusion _ a) := by
    intro a
    change P a 0 = f (oneBallIntervalHomeomorph (unitBoundaryInclusion _ a))
    rcases oneBoundary_eq a with rfl | rfl
    · rw [hP₀, oneBallIntervalHomeomorph_boundary]
      exact p₀.source
    · rw [hP₁, oneBallIntervalHomeomorph_boundary]
      exact p₁.source
  let G := ballHomotopyExtension F H h₀
  have he (b : Bool) : e.symm (boolEndpoint b) =
      unitBoundaryInclusion _ (oneBoundaryPoint b) := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (oneBallIntervalHomeomorph_boundary b).symm
  refine {
    map := G.comp ⟨fun z => (z.1, e.symm z.2),
      continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)⟩
    zero := ?_
    side_zero := ?_
    side_one := ?_ }
  · intro t
    change G (0, e.symm t) = f t
    rw [ballHomotopyExtension_zero]
    exact congrArg f (e.apply_symm_apply t)
  · intro τ
    change G (τ, e.symm (boolEndpoint false)) = p₀ τ
    rw [he, ballHomotopyExtension_boundary]
    change P (oneBoundaryPoint false) τ = p₀ τ
    rw [hP₀]
    rfl
  · intro τ
    change G (τ, e.symm (boolEndpoint true)) = p₁ τ
    rw [he, ballHomotopyExtension_boundary]
    change P (oneBoundaryPoint true) τ = p₁ τ
    rw [hP₁]
    rfl

end FiniteChains.RelativeAttachment
