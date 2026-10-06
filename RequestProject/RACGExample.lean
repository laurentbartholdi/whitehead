import RequestProject.RACGMedianGraph

/-!
# A concrete right-angled Coxeter group

Non-vacuity check for `RequestProject/RACGMedianGraph.lean`: the commutation graph on three
letters `0, 1, 2` in which only `0` and `1` commute.  The corresponding right-angled Coxeter
group is `(ℤ/2 × ℤ/2) * ℤ/2`; its Cayley graph is an infinite median graph.

* `FiniteChains.RACG.exampleA` — the commutation graph;
* `FiniteChains.RACG.exampleMedianGraph` — the median graph produced by the main construction;
* `FiniteChains.RACG.example_clen_gen`, `FiniteChains.RACG.example_clen_two` — the two shortest
  kinds of element really have length one and two, so the group is not trivial.
-/

namespace FiniteChains
namespace RACG

/-- The commutation graph on `Fin 3` in which exactly `0` and `1` commute. -/
def exampleA : CommRel (Fin 3) where
  rel i j := (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)
  rel_symm := by rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp
  rel_irrefl := by decide

theorem exampleA_dim (t : Finset (Fin 3))
    (_h : ∀ s ∈ t, ∀ r ∈ t, s ≠ r → exampleA.rel s r) : t.card ≤ 3 := by
  calc t.card ≤ (Finset.univ : Finset (Fin 3)).card := Finset.card_le_univ t
    _ = 3 := by simp

/-- The Cayley graph of this right-angled Coxeter group, as a median graph. -/
noncomputable def exampleMedianGraph : MedianGraph (CayGroup exampleA) :=
  medianGraph exampleA exampleA_dim

theorem example_isRed_single (s : Fin 3) : IsRed exampleA.rel [s] := ⟨trivial, by simp [canStart]⟩

/-- A generator has length one. -/
theorem example_clen_gen (s : Fin 3) : clen exampleA (gen exampleA s) = 1 := by
  have h : gen exampleA s = cword exampleA [s] := by simp
  rw [h, clen_cword exampleA (example_isRed_single s)]
  simp

/-- The product of two non-commuting generators has length two: the group is infinite, and in
particular not the trivial group. -/
theorem example_clen_two : clen exampleA (cword exampleA [0, 2]) = 2 := by
  have h : IsRed exampleA.rel [(0 : Fin 3), 2] := by
    refine ⟨example_isRed_single 2, ?_⟩
    rintro (h | ⟨h, -⟩)
    · exact absurd h (by simp)
    · rcases h with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact absurd h2 (by simp)
      · exact absurd h1 (by simp)
  rw [clen_cword exampleA h]
  simp

/-- The two vertices at distance one from the identity along the generator `s`. -/
theorem example_cdist_gen (s : Fin 3) : cdist exampleA 1 (gen exampleA s) = 1 := by
  simpa [cdist] using example_clen_gen s

end RACG
end FiniteChains
