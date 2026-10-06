module

public import RequestProject.NecessityAlgebraicMod
public import RequestProject.Fox

@[expose] public section

/-! The compactness argument needs finite attaching words, not finite cell sets. -/

namespace FiniteChains

/-- A Fox derivative has finite support in the generator index even when the generator
type is infinite: a free-group element contains only finitely many letters. -/
theorem fox_generator_support_finite {α : Type*} [DecidableEq α] (w : FreeGroup α) :
    {i : α | fox i w ≠ 0}.Finite := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of k =>
      apply (Set.finite_singleton k).subset
      intro i hi
      by_contra hn
      simp only [Set.mem_singleton_iff] at hn
      simp [fox_of, hn] at hi
  | inv_of k hk =>
      apply hk.subset
      intro i hi
      by_contra hz
      simp only [Set.mem_setOf_eq, not_not] at hz
      rw [Set.mem_setOf_eq, fox_inv, hz, mul_zero, neg_zero] at hi
      exact hi rfl
  | mul a b ha hb =>
      apply (ha.union hb).subset
      intro i hi
      by_contra hz
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hz
      simp [fox_mul, hz.1, hz.2] at hi

variable {G I J : Type*} [Group G] (b : I → J → MonoidAlgebra ℤ G)

/-- A finite chain has finite boundary whenever each individual cell has finite boundary. -/
theorem foxBoundary_support_finite
    (hcol : ∀ j, {i : I | b i j ≠ 0}.Finite) (v : J →₀ MonoidAlgebra ℤ G) :
    {i : I | foxBoundary b v i ≠ 0}.Finite := by
  classical
  apply (v.support.finite_toSet.biUnion (fun j _ => hcol j)).subset
  intro i hi
  simp only [Set.mem_setOf_eq] at hi
  simp only [Set.mem_iUnion, Finset.mem_coe]
  by_contra h
  apply hi
  unfold foxBoundary
  apply Finset.sum_eq_zero
  intro j hj
  have hz : b i j = 0 := by
    by_contra hn
    exact h ⟨j, hj, hn⟩
  rw [hz, mul_zero]

section Compactness

universe u

/-- Section 2's algebraic compactness conclusion for arbitrarily many cells. Only the
boundary of an individual cell must be finite; no finiteness assumption is imposed on
either cell-index type. -/
theorem exists_perfect_normal_foxSatMod_of_finite_columns
    {G I J : Type u} [Group G] (b : I → J → MonoidAlgebra ℤ G)
    (hchains : HasCellChainsLift b)
    (hcol : ∀ j, {i : I | b i j ≠ 0}.Finite)
    (htf : ∀ (N : Subgroup G) [N.Normal],
      (∀ p : ℕ, p.Prime → ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod p b v N) →
        IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆))) :
    ∃ N : Subgroup G, N.Normal ∧
      (∀ p : ℕ, p.Prime → ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod p b v N) ∧
      (∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v N) ∧ ⁅N, N⁆ = N :=
  exists_perfect_normal_foxSatMod hchains (foxBoundary_support_finite b hcol) hcol htf

end Compactness

end FiniteChains
