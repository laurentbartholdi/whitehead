module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.SquareSideQuotient
public import Mathlib.Topology.Homotopy.Path

@[expose] public section

/-! A genuine once-around interval parametrization of the square boundary.
Its only repeated point is the pair of interval endpoints, so based loop
homotopies descend to homotopies of attaching-circle maps.
Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval
open Set Topology

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.RelativeAttachment

def squareCorner00 : SquareBoundary := squareSideMap (0, false) 0
def squareCorner01 : SquareBoundary := squareSideMap (0, false) 1
def squareCorner11 : SquareBoundary := squareSideMap (0, true) 1
def squareCorner10 : SquareBoundary := squareSideMap (0, true) 0

def squareTraversalLeft : Path squareCorner00 squareCorner01 where
  toContinuousMap := squareSideMap (0, false)
  source' := rfl
  target' := rfl

def squareTraversalTop : Path squareCorner01 squareCorner11 where
  toContinuousMap := squareSideMap (1, true)
  source' := by apply Subtype.ext; funext i; fin_cases i <;> rfl
  target' := by apply Subtype.ext; funext i; fin_cases i <;> rfl

def squareTraversalRight : Path squareCorner11 squareCorner10 :=
  ({ toContinuousMap := squareSideMap (0, true)
     source' := rfl
     target' := rfl } : Path squareCorner10 squareCorner11).symm

def squareTraversalBottom : Path squareCorner10 squareCorner00 :=
  ({ toContinuousMap := squareSideMap (1, false)
     source' := by apply Subtype.ext; funext i; fin_cases i <;> rfl
     target' := by apply Subtype.ext; funext i; fin_cases i <;> rfl } :
      Path squareCorner00 squareCorner10).symm

/-- The balanced concatenation allocates one quarter of the interval to
each side, in positive once-around order. -/
def squareBoundaryTraversal : Path squareCorner00 squareCorner00 :=
  (squareTraversalLeft.trans squareTraversalTop).trans
    (squareTraversalRight.trans squareTraversalBottom)

theorem squareBoundaryTraversal_surjective : Function.Surjective squareBoundaryTraversal := by
  intro z
  obtain ⟨⟨s, t⟩, rfl⟩ := squareSideQuotient_surjective z
  change squareSideMap s t ∈ Set.range squareBoundaryTraversal
  simp only [squareBoundaryTraversal, Path.trans_range]
  rcases s with ⟨i, b⟩
  fin_cases i <;> cases b
  · exact Or.inl (Or.inl ⟨t, rfl⟩)
  · exact Or.inr (Or.inl ⟨unitInterval.symm t, by
      simp [squareTraversalRight]⟩)
  · exact Or.inr (Or.inr ⟨unitInterval.symm t, by
      simp [squareTraversalBottom]⟩)
  · exact Or.inl (Or.inr ⟨t, rfl⟩)

/-- There is no hidden multiple traversal: only zero and one coincide. -/
theorem squareBoundaryTraversal_fiber {s t : I}
    (h : squareBoundaryTraversal s = squareBoundaryTraversal t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  have coords (u : I) :
      (((squareBoundaryTraversal u).val 0 : ℝ), ((squareBoundaryTraversal u).val 1 : ℝ)) =
        if (u : ℝ) ≤ 1 / 2 then
          if 2 * (u : ℝ) ≤ 1 / 2 then (0, 4 * (u : ℝ)) else (4 * (u : ℝ) - 1, 1)
        else if 2 * (u : ℝ) - 1 ≤ 1 / 2 then (1, 3 - 4 * (u : ℝ))
        else (4 - 4 * (u : ℝ), 0) := by
    simp only [squareBoundaryTraversal, Path.trans_apply]
    by_cases hu : (u : ℝ) ≤ 1 / 2
    · rw [dif_pos hu, if_pos hu]
      by_cases hv : 2 * (u : ℝ) ≤ 1 / 2
      · rw [dif_pos hv, if_pos hv]
        simp [squareTraversalLeft, squareSideMap, Whitehead.squareEdge, boolEndpoint]
        ring
      · rw [dif_neg hv, if_neg hv]
        simp [squareTraversalTop, squareSideMap, Whitehead.squareEdge, boolEndpoint]
        ring
    · rw [dif_neg hu, if_neg hu]
      by_cases hv : 2 * (u : ℝ) - 1 ≤ 1 / 2
      · rw [dif_pos hv, if_pos hv]
        simp [squareTraversalRight, squareSideMap, Whitehead.squareEdge, boolEndpoint,
          Path.symm_apply, Function.comp_apply, unitInterval.coe_symm_eq]
        ring
      · rw [dif_neg hv, if_neg hv]
        simp [squareTraversalBottom, squareSideMap, Whitehead.squareEdge, boolEndpoint,
          Path.symm_apply, Function.comp_apply, unitInterval.coe_symm_eq]
        ring
  have he := (coords s).symm.trans
    ((congrArg (fun z : SquareBoundary => ((z.val 0 : ℝ), (z.val 1 : ℝ))) h).trans (coords t))
  have hs₀ := s.property.1
  have hs₁ := s.property.2
  have ht₀ := t.property.1
  have ht₁ := t.property.2
  split_ifs at he <;> simp only [Prod.mk.injEq] at he <;> rcases he with ⟨h₀, h₁⟩ <;>
    first
    | exact Or.inl (Subtype.ext (by linarith))
    | exact Or.inr (Or.inl ⟨Subtype.ext (show (s : ℝ) = 0 by linarith),
        Subtype.ext (show (t : ℝ) = 1 by linarith)⟩)
    | exact Or.inr (Or.inr ⟨Subtype.ext (show (s : ℝ) = 1 by linarith),
        Subtype.ext (show (t : ℝ) = 0 by linarith)⟩)

theorem squareBoundaryTraversal_isQuotientMap : IsQuotientMap squareBoundaryTraversal :=
  squareBoundaryTraversal.continuous.isClosedMap.isQuotientMap
    squareBoundaryTraversal.continuous squareBoundaryTraversal_surjective

variable {X : Type} [TopologicalSpace X]

def squareLoopDesc {x : X} (p : Path x x) : C(SquareBoundary, X) where
  toFun z := p (Function.surjInv squareBoundaryTraversal_surjective z)
  continuous_toFun := by
    apply squareBoundaryTraversal_isQuotientMap.continuous_iff.mpr
    have he : (fun z => p (Function.surjInv squareBoundaryTraversal_surjective z)) ∘
        squareBoundaryTraversal = p := by
      funext t
      change p (Function.surjInv squareBoundaryTraversal_surjective (squareBoundaryTraversal t)) = p t
      have h := Function.surjInv_eq squareBoundaryTraversal_surjective (squareBoundaryTraversal t)
      rcases squareBoundaryTraversal_fiber h with h | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
      · exact congrArg p h
      · rw [h₀, h₁, p.source, p.target]
      · rw [h₀, h₁, p.source, p.target]
    rw [he]
    exact p.continuous

@[simp] theorem squareLoopDesc_traversal {x : X} (p : Path x x) (t : I) :
    squareLoopDesc p (squareBoundaryTraversal t) = p t := by
  have h := Function.surjInv_eq squareBoundaryTraversal_surjective (squareBoundaryTraversal t)
  rcases squareBoundaryTraversal_fiber h with h | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
  · exact congrArg p h
  · change p _ = p t
    rw [h₀, h₁, p.source, p.target]
  · change p _ = p t
    rw [h₀, h₁, p.source, p.target]

theorem squareLoopDesc_map (f : C(SquareBoundary, X)) :
    squareLoopDesc (squareBoundaryTraversal.map f.continuous) = f := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, rfl⟩ := squareBoundaryTraversal_surjective z
  exact squareLoopDesc_traversal _ t

/-- A homotopy of based traversal loops gives a homotopy of the actual
attaching maps; equality of group words is never used as a substitute. -/
def squareLoopDescHomotopy {x : X} {p q : Path x x} (H : p.Homotopy q) :
    (squareLoopDesc p).Homotopy (squareLoopDesc q) := by
  let F : C(I, C(I, X)) := (H.toHomotopy.toContinuousMap.comp
    ⟨Prod.swap, continuous_swap⟩).curry
  let D : C(SquareBoundary, C(I, X)) := {
    toFun z := F (Function.surjInv squareBoundaryTraversal_surjective z)
    continuous_toFun := by
      apply squareBoundaryTraversal_isQuotientMap.continuous_iff.mpr
      have he : (fun z => F (Function.surjInv squareBoundaryTraversal_surjective z)) ∘
          squareBoundaryTraversal = F := by
        funext s
        apply ContinuousMap.ext
        intro τ
        have hs := Function.surjInv_eq squareBoundaryTraversal_surjective (squareBoundaryTraversal s)
        rcases squareBoundaryTraversal_fiber hs with hs | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
        · exact congrArg (fun z => H (τ, z)) hs
        · change H (τ, _) = H (τ, s)
          rw [h₀, h₁, H.source, H.target]
        · change H (τ, _) = H (τ, s)
          rw [h₀, h₁, H.source, H.target]
      rw [he]
      exact F.continuous }
  exact {
    toContinuousMap := D.uncurry.comp ⟨Prod.swap, continuous_swap⟩
    map_zero_left := fun z => H.apply_zero _
    map_one_left := fun z => H.apply_one _ }

theorem squareLoopDesc_homotopic {x : X} {p q : Path x x} (H : p.Homotopic q) :
    (squareLoopDesc p).Homotopic (squareLoopDesc q) :=
  Nonempty.map squareLoopDescHomotopy H

end FiniteChains.RelativeAttachment
