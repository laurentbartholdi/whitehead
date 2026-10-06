import RequestProject.CoverComplexPres

/-!
# The universal cover of a presentation complex and its two-cycles

The two-cells of a presentation complex `K` carry, over the universal cover, the module
`π₂(K) = H₂(K̃) = ker ∂₂`; this is the module the requirements (2.2) and the chain
condition of Theorem A speak about.  In the combinatorial model the universal cover is the
cover attached to the relator subgroup `R = ⟪ρ⟫` (whose deck group is `G = π₁(K) = F/R`),
and this file identifies its two-cycles: a cellular two-chain of `K̃` is a cycle exactly
when its coordinate vector over `ℤ[G]` is killed by the Fox matrix
(`FiniteChains.Comb.univCover_bdry2_eq_zero_iff`).

This is the precise form of the statement "`π₂ = ker ∂₂`" used throughout Section 2: the
condition assumed of a chain of presentation complexes (the inclusions are zero on `π₂`)
is exactly the vanishing of the image of such a cycle.
-/

namespace FiniteChains
namespace Comb

open MonoidAlgebra

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]
variable {J : Type u} [Fintype J] [DecidableEq J] (ρ : J → FreeGroup α)

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] in
theorem rel_mem_relSub (j : J) : ρ j ∈ relSub ρ :=
  Subgroup.subset_normalClosure (Set.mem_range_self j)

/-- The universal cover of the presentation complex: the cover attached to the relator
subgroup, with deck group `G = π₁(K)`. -/
noncomputable abbrev univCover : Complex2.{u} :=
  coverComplex (relSub ρ) ρ (rel_mem_relSub ρ)

/-- **The two-cycles of the universal cover.**  A cellular two-chain of `K̃` is a cycle
exactly when its coordinate vector over `ℤ[G]` is killed by the Fox matrix of the
presentation; that is, `π₂(K) = ker ∂₂` in explicit coordinates. -/
theorem univCover_bdry2_eq_zero_iff (u : ((FreeGroup α ⧸ relSub ρ) × J) →₀ ℤ) :
    Comb.bdry2 (univCover ρ) u = 0 ↔
      ∀ i : α, ∑ j : J, (coords (relSub ρ) J u) j * foxMatrixPres ρ i j = 0 := by
  constructor
  · intro h
    have h' : _root_.FiniteChains.bdry2 (relSub ρ) ρ (coords (relSub ρ) J u) = 0 := by
      rw [coverComplex_bdry2 (rel_mem_relSub ρ), h, map_zero]
    intro i
    have := congrFun h' i
    simpa [_root_.FiniteChains.bdry2, foxMatrixPres, proj_eq_quotRingHom] using this
  · intro h
    have h' : _root_.FiniteChains.bdry2 (relSub ρ) ρ (coords (relSub ρ) J u) = 0 := by
      funext i
      simpa [_root_.FiniteChains.bdry2, foxMatrixPres, proj_eq_quotRingHom] using h i
    rw [coverComplex_bdry2 (rel_mem_relSub ρ)] at h'
    refine (coords (relSub ρ) α).injective ?_
    rw [h']
    exact (map_zero _).symm

end Comb
end FiniteChains
