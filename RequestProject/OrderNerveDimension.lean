module

public import RequestProject.MathlibOrderNerveCells
public import RequestProject.OrderComplexSurface
public import Mathlib.AlgebraicTopology.SimplicialSet.Dimension

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory Simplicial
universe u

/-- A bounded strictly increasing rank bounds the dimension of every actual
nondegenerate simplex of the poset nerve. -/
theorem orderNerve_nonDegenerate_dimension_le {P : Type u} [PartialOrder P]
    (rank : P → ℕ) (hrank : StrictMono rank) (d : ℕ) (hbound : ∀ p, rank p ≤ d)
    {n : ℕ} (s : (nerve P) _⦋n⦌) (hs : s ∈ (nerve P).nonDegenerate n) : n ≤ d := by
  have hstrict := hrank.comp ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s).mp hs)
  let g : Fin (n + 1) → Fin (d + 1) := fun i => ⟨rank (s.obj i), Nat.lt_succ_of_le (hbound _)⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply hstrict.injective
    exact congrArg Fin.val hij
  have hcard := Fintype.card_le_of_injective g hg
  simp only [Fintype.card_fin] at hcard
  omega

/-- The actual Mathlib nerve of a bounded ranked poset has the asserted dimension. -/
theorem orderNerve_hasDimensionLE {P : Type u} [PartialOrder P]
    (rank : P → ℕ) (hrank : StrictMono rank) (d : ℕ) (hbound : ∀ p, rank p ≤ d) :
    (nerve P).HasDimensionLE d := by
  constructor
  intro n hn
  apply Set.eq_univ_of_forall
  intro s
  rw [SSet.mem_degenerate_iff_notMem_nonDegenerate]
  intro hs
  have h := orderNerve_nonDegenerate_dimension_le rank hrank d hbound s hs
  omega

/-- The actual nerve of each project surface cell poset is at most two-dimensional. -/
theorem surfaceRank_orderNerve_hasDimensionLE {P : Type u} [PartialOrder P]
    (r : FiniteChains.ASC.SurfaceRank P) : (nerve P).HasDimensionLE 2 :=
  orderNerve_hasDimensionLE r.rk (fun _ _ h => r.rk_lt_of_lt h) 2 r.rk_le_two

end FiniteChains.Comb
