import RequestProject.FoxWordPrefixSum
import RequestProject.CoverChainComplex

namespace FiniteChains
variable {α : Type*} [DecidableEq α]
  (N : Subgroup (FreeGroup α)) [N.Normal]

/-- Projected Fox coefficients are the signed group-ring incidences at actual word prefixes. -/
theorem coverFox_mk_prefix_sum (i : α) (l : List (α × Bool)) :
    proj N (fox i (FreeGroup.mk l)) =
      ∑ k : Fin l.length,
        if i = l[k.val].1 then
          MonoidAlgebra.single
            ((QuotientGroup.mk (FreeGroup.mk (l.take k.val)) : FreeGroup α ⧸ N) *
              (if l[k.val].2 then 1 else
                (QuotientGroup.mk (FreeGroup.of l[k.val].1) : FreeGroup α ⧸ N)⁻¹))
            (if l[k.val].2 then (1 : ℤ) else -1)
        else 0 := by
  classical
  rw [fox_mk_prefix_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hi : i = l[k.val].1
  · cases hb : l[k.val].2 <;>
      simp [foxWordIncidence, hi, hb, map_neg,
        MonoidAlgebra.single_mul_single, grp_eq_single, proj_single,
        QuotientGroup.mk_inv]
  · simp [foxWordIncidence, hi]

end FiniteChains
