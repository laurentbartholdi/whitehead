import RequestProject.CombHurewicz1Pres

/-! Integral chain witnesses for edge-path homotopies in arbitrary cellular two-complexes. -/

namespace FiniteChains.Comb
universe u
variable {X : Complex2.{u}}

theorem pathChain_revPath (p : List (X.E × Bool)) :
    pathChain (revPath p) = -pathChain p := by
  induction p with
  | nil => simp
  | cons e p ih =>
    rw [revPath_cons, pathChain_append, ih, pathChain_cons]
    obtain ⟨e, b⟩ := e
    cases b <;> simp [revGerm, pathChain_cons]

/-- An elementary path cancellation has an explicit cellular two-chain witness. -/
theorem Cancels.exists_boundary {p q : List (X.E × Bool)} (h : Cancels X p q) :
    ∃ c : X.F →₀ ℤ, bdry2 X c = pathChain p - pathChain q := by
  rcases h with ⟨l, r, e, rfl, rfl⟩ | ⟨l, r, f, rfl, rfl⟩
  · refine ⟨0, ?_⟩
    obtain ⟨e, b⟩ := e
    cases b <;> simp [pathChain_append, pathChain_cons, revGerm]
  · refine ⟨Finsupp.single f 1, ?_⟩
    rw [bdry2_single, one_smul, pathChain_append, pathChain_append, pathChain_append]
    abel

/-- Homotopic paths differ by the boundary of a finitely supported integral two-chain. -/
theorem Htpy.exists_boundary {a b : X.V} {p q : List (X.E × Bool)}
    (h : Htpy X a b p q) :
    ∃ c : X.F →₀ ℤ, bdry2 X c = pathChain p - pathChain q := by
  induction h with
  | refl => exact ⟨0, by simp⟩
  | @tail q r h hstep ih =>
    obtain ⟨c, hc⟩ := ih
    have hs : ∃ d : X.F →₀ ℤ, bdry2 X d = pathChain q - pathChain r := by
      rcases hstep with hs | hs
      · exact hs.2.2.exists_boundary
      · obtain ⟨d, hd⟩ := hs.2.2.exists_boundary
        exact ⟨-d, by rw [map_neg, hd]; abel⟩
    obtain ⟨d, hd⟩ := hs
    refine ⟨c + d, ?_⟩
    rw [map_add, hc, hd]
    abel

end FiniteChains.Comb
