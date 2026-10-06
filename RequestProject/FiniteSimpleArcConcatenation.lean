import RequestProject.SimpleLoopBoundaryHomeomorph
import Mathlib.Topology.Subpath
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-! Nonempty finite concatenation without an inserted constant initial or
terminal segment. It preserves injectivity when different arcs only meet
at consecutive endpoints. This is the parameter used for actual finite
circle homeomorphisms. Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval
open Set

namespace FiniteChains.RelativeAttachment

variable {X : Type} [TopologicalSpace X]

/-- `n+1` arcs, with no artificial stationary part. -/
def arcConcat : (n : ℕ) → (v : Fin (n + 2) → X) →
    (∀ i : Fin (n + 1), Path (v i.castSucc) (v i.succ)) → Path (v 0) (v (Fin.last (n + 1)))
  | 0, _, F => F 0
  | n + 1, v, F =>
      (arcConcat n (v ∘ Fin.castSucc) (fun i => F i.castSucc)).trans (F (Fin.last (n + 1)))

theorem arcConcat_homotopic_concat (n : ℕ) (v : Fin (n + 2) → X)
    (F : ∀ i : Fin (n + 1), Path (v i.castSucc) (v i.succ)) :
    (arcConcat n v F).Homotopic (Path.concat v F) := by
  induction n with
  | zero =>
    rw [Path.concat_succ, Path.concat_zero]
    exact (Path.Homotopic.refl_trans (F 0)).symm
  | succ n ih =>
    rw [Path.concat_succ]
    exact (ih (v ∘ Fin.castSucc) (fun i => F i.castSucc)).hcomp
      (Path.Homotopic.refl (F (Fin.last (n + 1))))

theorem arcConcat_range (n : ℕ) (v : Fin (n + 2) → X)
    (F : ∀ i : Fin (n + 1), Path (v i.castSucc) (v i.succ)) (x : X) :
    x ∈ Set.range (arcConcat n v F) ↔ ∃ i, x ∈ Set.range (F i) := by
  induction n with
  | zero =>
    constructor
    · intro hx
      exact ⟨0, hx⟩
    · rintro ⟨i, hi⟩
      have hi0 : i = 0 := Fin.ext (by omega)
      subst i
      exact hi
  | succ n ih =>
    change x ∈ Set.range
      ((arcConcat n (v ∘ Fin.castSucc) (fun i => F i.castSucc)).trans (F (Fin.last (n + 1)))) ↔ _
    rw [Path.trans_range, Set.mem_union, ih]
    constructor
    · rintro (⟨i, hi⟩ | hlast)
      · exact ⟨i.castSucc, hi⟩
      · exact ⟨Fin.last (n + 1), hlast⟩
    · rintro ⟨i, hi⟩
      refine Fin.lastCases (fun hi => Or.inr hi)
        (fun j hj => Or.inl ⟨j, hj⟩) i hi

theorem arcConcat_injective (n : ℕ) (v : Fin (n + 2) → X)
    (F : ∀ i : Fin (n + 1), Path (v i.castSucc) (v i.succ))
    (hF : ∀ i, Function.Injective (F i))
    (hmeet : ∀ i j : Fin (n + 1), i < j → ∀ s t : I,
      F i s = F j t → s = 1 ∧ t = 0) : Function.Injective (arcConcat n v F) := by
  induction n with
  | zero => exact hF 0
  | succ n ih =>
    apply path_trans_injective
    · exact ih (v ∘ Fin.castSucc) (fun i => F i.castSucc)
        (fun i => hF i.castSucc)
        (fun i j hij s t h => hmeet i.castSucc j.castSucc hij s t h)
    · exact hF (Fin.last (n + 1))
    · intro s t h
      obtain ⟨i, u, hu⟩ := (arcConcat_range n (v ∘ Fin.castSucc)
        (fun i => F i.castSucc) _).mp ⟨s, rfl⟩
      have ht : t = 0 := (hmeet i.castSucc (Fin.last (n + 1))
        (by exact Fin.castSucc_lt_last i) u t (hu.trans h)).2
      rw [ht, (F (Fin.last (n + 1))).source] at h
      exact h

end FiniteChains.RelativeAttachment
