import RequestProject.ReducedSimplex
import Mathlib.Analysis.Normed.Operator.Banach

namespace FiniteChains

/-- The strict-coordinate description is exactly the reduced simplex interior. -/
theorem reducedSimplex_interior_eq (n : ℕ) :
    interior (reducedSimplex n) = reducedSimplexPositive n := by
  apply Set.Subset.antisymm
  · intro x hx
    constructor
    · intro i
      have hi := interior_mono (show reducedSimplex n ⊆
          (Function.eval i : (Fin n → ℝ) → ℝ) ⁻¹' Set.Ici 0 from fun _ h => h.1 i) hx
      have ht := (isOpenMap_eval i).interior_preimage_subset_preimage_interior hi
      simpa only [Set.mem_preimage, interior_Ici, Set.mem_Ioi, Function.eval] using ht
    · cases n with
      | zero => simp
      | succ n =>
        let L : (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
          { toFun := fun y => ∑ i, y i
            map_add' := by intro y z; simp [Finset.sum_add_distrib]
            map_smul' := by intro a y; simp [Finset.mul_sum]
            cont := continuous_finset_sum _ (fun i _ => continuous_apply i) }
        have hs : Function.Surjective L := by
          intro r
          refine ⟨Pi.single (0 : Fin (n + 1)) r, ?_⟩
          simp [L, Pi.single_apply, Finset.sum_ite_eq']
        have hi := interior_mono (show reducedSimplex (n + 1) ⊆
            L ⁻¹' Set.Iic 1 from fun _ h => h.2) hx
        have ht := (L.isOpenMap hs).interior_preimage_subset_preimage_interior hi
        have ht' : L x < 1 := by simpa only [Set.mem_preimage, interior_Iic, Set.mem_Iio] using ht
        exact ht'
  · exact interior_maximal (reducedSimplexPositive_subset n) (reducedSimplexPositive_isOpen n)

/-- Reinserted barycentric coordinates are all positive exactly on the reduced simplex interior. -/
theorem reducedSimplexToStandard_positive_iff (n : ℕ) (x : reducedSimplex n) :
    (∀ i, 0 < (reducedSimplexToStandard n x).val i) ↔ x.val ∈ interior (reducedSimplex n) := by
  rw [reducedSimplex_interior_eq]
  change (∀ i : Fin (n + 1), 0 < (Fin.cons (1 - (∑ j : Fin n, x.val j)) x.val : Fin (n + 1) → ℝ) i) ↔
    (∀ j, 0 < x.val j) ∧ ∑ j, x.val j < 1
  constructor
  · intro h
    constructor
    · intro j
      simpa using h j.succ
    · have h0 := h 0
      simp only [Fin.cons_zero] at h0
      linarith
  · rintro ⟨hp, hs⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using sub_pos.mpr hs
    · simpa using hp j

/-- Reduced-simplex frontier points correspond exactly to standard-simplex boundary points. -/
theorem reducedSimplexToStandard_frontier_iff (n : ℕ) (x : reducedSimplex n) :
    x.val ∈ frontier (reducedSimplex n) ↔
      ¬ ∀ i, 0 < (reducedSimplexToStandard n x).val i := by
  rw [reducedSimplexToStandard_positive_iff]
  simp only [frontier, (reducedSimplex_isClosed n).closure_eq,
    Set.mem_diff, x.property, true_and]

end FiniteChains
