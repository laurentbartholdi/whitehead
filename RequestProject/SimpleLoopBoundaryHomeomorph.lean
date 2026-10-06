import RequestProject.SquareBoundaryLoopQuotient
import RequestProject.SquareBoundaryNormHomeomorph

/-! Elementary simple-arc gluing and an explicit homeomorphism from the
actual normed-circle boundary onto a once-traversed Hausdorff simple loop.
The proof uses the concrete interval quotient, not a classification theorem.
Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval
open Set Topology

namespace FiniteChains.RelativeAttachment

variable {X : Type} [TopologicalSpace X]

theorem path_trans_injective {a b c : X} (p : Path a b) (q : Path b c)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hmeet : ∀ s t : I, p s = q t → p s = b) : Function.Injective (p.trans q) := by
  intro s t h
  by_cases hs : (s : ℝ) ≤ 1 / 2 <;> by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [Path.trans_apply, Path.trans_apply, dif_pos hs, dif_pos ht] at h
    have hv := congrArg (fun z : I => (z : ℝ)) (hp h)
    apply Subtype.ext
    dsimp at hv
    linarith
  · rw [Path.trans_apply, Path.trans_apply, dif_pos hs, dif_neg ht] at h
    have hb := hmeet _ _ h
    have hv := congrArg (fun z : I => (z : ℝ)) (hp (hb.trans p.target.symm))
    have hw := congrArg (fun z : I => (z : ℝ)) (hq ((h.symm.trans hb).trans q.source.symm))
    apply Subtype.ext
    dsimp at hv hw
    linarith
  · rw [Path.trans_apply, Path.trans_apply, dif_neg hs, dif_pos ht] at h
    have hb := hmeet _ _ h.symm
    have hv := congrArg (fun z : I => (z : ℝ)) (hp (hb.trans p.target.symm))
    have hw := congrArg (fun z : I => (z : ℝ)) (hq ((h.trans hb).trans q.source.symm))
    apply Subtype.ext
    dsimp at hv hw
    linarith
  · rw [Path.trans_apply, Path.trans_apply, dif_neg hs, dif_neg ht] at h
    have hv := congrArg (fun z : I => (z : ℝ)) (hq h)
    apply Subtype.ext
    dsimp at hv
    linarith

/-- Two arcs meeting only at their endpoints form a loop with exactly the
expected endpoint identification. -/
theorem path_trans_loop_fiber {a b : X} (p : Path a b) (q : Path b a)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hmeet : ∀ s t : I, p s = q t → p s = a ∨ p s = b)
    {s t : I} (h : (p.trans q) s = (p.trans q) t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  by_cases hs : (s : ℝ) ≤ 1 / 2 <;> by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [Path.trans_apply, Path.trans_apply, dif_pos hs, dif_pos ht] at h
    have hv := congrArg (fun z : I => (z : ℝ)) (hp h)
    exact Or.inl (Subtype.ext (by dsimp at hv; linarith))
  · rw [Path.trans_apply, Path.trans_apply, dif_pos hs, dif_neg ht] at h
    rcases hmeet _ _ h with ha | hb
    · have hv := congrArg (fun z : I => (z : ℝ)) (hp (ha.trans p.source.symm))
      have hw := congrArg (fun z : I => (z : ℝ)) (hq ((h.symm.trans ha).trans q.target.symm))
      exact Or.inr (Or.inl ⟨Subtype.ext (by change (s : ℝ) = 0; dsimp at hv; linarith),
        Subtype.ext (by change (t : ℝ) = 1; dsimp at hw; linarith)⟩)
    · have hv := congrArg (fun z : I => (z : ℝ)) (hp (hb.trans p.target.symm))
      have hw := congrArg (fun z : I => (z : ℝ)) (hq ((h.symm.trans hb).trans q.source.symm))
      exact Or.inl (Subtype.ext (by dsimp at hv hw; linarith))
  · rw [Path.trans_apply, Path.trans_apply, dif_neg hs, dif_pos ht] at h
    rcases hmeet _ _ h.symm with ha | hb
    · have hv := congrArg (fun z : I => (z : ℝ)) (hp (ha.trans p.source.symm))
      have hw := congrArg (fun z : I => (z : ℝ)) (hq ((h.trans ha).trans q.target.symm))
      exact Or.inr (Or.inr ⟨Subtype.ext (by change (s : ℝ) = 1; dsimp at hw; linarith),
        Subtype.ext (by change (t : ℝ) = 0; dsimp at hv; linarith)⟩)
    · have hv := congrArg (fun z : I => (z : ℝ)) (hp (hb.trans p.target.symm))
      have hw := congrArg (fun z : I => (z : ℝ)) (hq ((h.trans hb).trans q.source.symm))
      exact Or.inl (Subtype.ext (by dsimp at hv hw; linarith))
  · rw [Path.trans_apply, Path.trans_apply, dif_neg hs, dif_neg ht] at h
    have hv := congrArg (fun z : I => (z : ℝ)) (hq h)
    exact Or.inl (Subtype.ext (by dsimp at hv; linarith))

theorem squareLoopDesc_bijective {a : X} (p : Path a a)
    (hsur : Function.Surjective p)
    (hfiber : ∀ s t : I, p s = p t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :
    Function.Bijective (squareLoopDesc p) := by
  constructor
  · intro x y h
    obtain ⟨s, rfl⟩ := squareBoundaryTraversal_surjective x
    obtain ⟨t, rfl⟩ := squareBoundaryTraversal_surjective y
    rw [squareLoopDesc_traversal, squareLoopDesc_traversal] at h
    rcases hfiber s t h with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact squareBoundaryTraversal.source.trans squareBoundaryTraversal.target.symm
    · exact squareBoundaryTraversal.target.trans squareBoundaryTraversal.source.symm
  · intro x
    obtain ⟨t, rfl⟩ := hsur x
    exact ⟨squareBoundaryTraversal t, squareLoopDesc_traversal p t⟩

def simpleLoopSquareHomeomorph [T2Space X] {a : X} (p : Path a a)
    (hsur : Function.Surjective p)
    (hfiber : ∀ s t : I, p s = p t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :
    SquareBoundary ≃ₜ X := by
  letI : CompactSpace SquareBoundary := ⟨by
    simpa only [Set.range_eq_univ.mpr squareBoundaryTraversal_surjective] using
      (isCompact_range squareBoundaryTraversal.continuous)⟩
  exact Continuous.homeoOfEquivCompactToT2 (f :=
    Equiv.ofBijective (squareLoopDesc p) (squareLoopDesc_bijective p hsur hfiber))
    (squareLoopDesc p).continuous

def simpleLoopBoundaryHomeomorph [T2Space X] {a : X} (p : Path a a)
    (hsur : Function.Surjective p)
    (hfiber : ∀ s t : I, p s = p t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :
    UnitBoundary (Fin 2 → ℝ) ≃ₜ X :=
  unitBoundarySquareHomeomorph.trans (simpleLoopSquareHomeomorph p hsur hfiber)

@[simp] theorem simpleLoopSquareHomeomorph_traversal [T2Space X] {a : X} (p : Path a a)
    (hsur : Function.Surjective p)
    (hfiber : ∀ s t : I, p s = p t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) (t : I) :
    simpleLoopSquareHomeomorph p hsur hfiber (squareBoundaryTraversal t) = p t :=
  squareLoopDesc_traversal p t

end FiniteChains.RelativeAttachment
