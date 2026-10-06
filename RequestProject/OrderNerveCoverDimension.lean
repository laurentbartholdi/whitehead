import RequestProject.OrderNerveRealizationCovering

namespace FiniteChains.Comb
open CategoryTheory Simplicial

namespace IsPosetCover
variable {P Q : Type} [PartialOrder P] [PartialOrder Q] {f : P → Q}

/-- A genuine poset covering preserves the simplicial dimension bound upstairs. -/
theorem realization_hasDimensionLE (hf : IsPosetCover f) (d : ℕ)
    [(nerve Q).HasDimensionLE d] : (nerve P).HasDimensionLE d := by
  constructor
  intro n hn
  apply Set.eq_univ_of_forall
  intro s
  rw [SSet.mem_degenerate_iff_notMem_nonDegenerate]
  intro hs
  let t := (nerveMap hf.mono.functor).app _ s
  have ht : t ∈ (nerve Q).nonDegenerate n := by
    apply (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono t).mpr
    exact hf.strictMono.comp
      ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s).mp hs)
  have hdim := (nerve Q).dim_le_of_nonDegenerate ⟨t, ht⟩ d
  omega

end IsPosetCover
end FiniteChains.Comb
