import RequestProject.MomentAngle

/-! Finitely supported simplicial boundaries and the cubical coefficient convention. -/

namespace FiniteChains
variable {V : Type} [DecidableEq V] [LinearOrder V]

/-- The oriented boundary of a simplex, with each vertex ordered by its coordinate. -/
noncomputable def finiteSetBoundary : (Finset V →₀ ℤ) →ₗ[ℤ] (Finset V →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun σ => ∑ j ∈ σ,
    ((-1 : ℤ) ^ ((σ.erase j).filter (fun i => i < j)).card) •
      Finsupp.single (σ.erase j) 1)

@[simp] theorem finiteSetBoundary_single (σ : Finset V) (n : ℤ) :
    finiteSetBoundary (Finsupp.single σ n) = n • ∑ j ∈ σ,
      ((-1 : ℤ) ^ ((σ.erase j).filter (fun i => i < j)).card) •
        Finsupp.single (σ.erase j) 1 := by
  simp [finiteSetBoundary]

/-- The coordinate orientation agrees with the alternating boundary of an ordered triangle. -/
theorem finiteSetBoundary_triangle {a b c : V} (hab : a < b) (hbc : b < c) (n : ℤ) :
    finiteSetBoundary (Finsupp.single {a, b, c} n) =
      Finsupp.single {b, c} n - Finsupp.single {a, c} n + Finsupp.single {a, b} n := by
  have hac := hab.trans hbc
  have hbc' : b ≠ c := hbc.ne
  have hab' : a ≠ b := hab.ne
  have hac' : a ≠ c := hac.ne
  ext τ
  simp_all [finiteSetBoundary_single,
    Finset.erase_insert_of_ne, Finset.filter_insert, Finset.filter_singleton,
    not_lt_of_ge hab.le, not_lt_of_ge hbc.le, not_lt_of_ge hac.le]
  ring

variable [Fintype V]

omit [LinearOrder V] in
private theorem simplex_sum_univ (σ : Finset V) (f : V → ℤ) :
    (∑ j ∈ σ, f j) = ∑ j : V, if j ∈ σ then f j else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp

/-- The finitely supported differential has exactly the coefficient formula used by
the moment-angle and truncated-cube differentials. -/
theorem finiteSetBoundary_apply (c : Finset V →₀ ℤ) (τ : Finset V) :
    finiteSetBoundary c τ = simpBdry (fun σ => c σ) τ := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp [simpBdry]
  | add c d hc hd =>
    simp only [map_add, Finsupp.add_apply, hc, hd, simpBdry, mul_add,
      Finset.sum_add_distrib]
  | single σ n =>
    simp only [finiteSetBoundary_single, Finsupp.smul_apply, Finsupp.finset_sum_apply,
      smul_eq_mul, Finsupp.single_apply, simpBdry]
    rw [simplex_sum_univ, Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hjσ : j ∈ σ
    · by_cases hjτ : j ∈ τ
      · have he : σ.erase j ≠ τ := by
          intro he
          have hh : j ∉ σ.erase j := Finset.notMem_erase _ _
          exact hh (he.symm ▸ hjτ)
        simp [hjσ, hjτ, he]
      · by_cases he : σ.erase j = τ
        · have hi : insert j τ = σ := by rw [← he, Finset.insert_erase hjσ]
          simp [hjσ, hjτ, he, hi]
          ring
        · have hi : insert j τ ≠ σ := by
            intro hi
            apply he
            rw [← hi, Finset.erase_insert hjτ]
          simp [hjσ, hjτ, he, Ne.symm hi]
    · have hi : insert j τ ≠ σ := by
        intro hi
        exact hjσ (hi ▸ Finset.mem_insert_self j τ)
      simp [hjσ, Ne.symm hi]

/-- Equality of the finitely supported and coefficient-function cycle conditions. -/
theorem finiteSetBoundary_eq_zero_iff (c : Finset V →₀ ℤ) :
    finiteSetBoundary c = 0 ↔ simpBdry (fun σ => c σ) = 0 := by
  constructor
  · intro h
    funext τ
    rw [← finiteSetBoundary_apply, h]
    rfl
  · intro h
    ext τ
    rw [finiteSetBoundary_apply, h]
    rfl

end FiniteChains
