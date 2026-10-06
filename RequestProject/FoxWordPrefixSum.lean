import RequestProject.FoxWordBoundary

namespace FiniteChains
variable {α : Type*} [DecidableEq α]

/-- The actual Fox word boundary is its finite signed-prefix sum. -/
theorem foxWordPathBoundary_prefix_sum (i : α) (g : FreeGroup α)
    (l : List (α × Bool)) :
    foxWordPathBoundary i g l =
      ∑ k : Fin l.length, grp (g * FreeGroup.mk (l.take k.val)) *
        foxWordIncidence i l[k.val] := by
  induction l generalizing g with
  | nil => simp [foxWordPathBoundary]
  | cons p l ih =>
    rw [foxWordPathBoundary, ih]
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.take_zero, ← FreeGroup.one_eq_mk, mul_one,
      List.getElem_cons_zero, Fin.val_succ, List.take_succ_cons, List.getElem_cons_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    have hm : FreeGroup.mk (p :: l.take k.val) =
        foxWordLetter p * FreeGroup.mk (l.take k.val) := by
      rw [← fox_mk_single_letter, FreeGroup.mul_mk]
      rfl
    rw [hm, mul_assoc]

/-- The actual Fox derivative is the finite signed-prefix sum at the identity. -/
theorem fox_mk_prefix_sum (i : α) (l : List (α × Bool)) :
    fox i (FreeGroup.mk l) =
      ∑ k : Fin l.length, grp (FreeGroup.mk (l.take k.val)) *
        foxWordIncidence i l[k.val] := by
  rw [← foxWordPathBoundary_one]
  simpa only [one_mul] using foxWordPathBoundary_prefix_sum i 1 l

end FiniteChains
