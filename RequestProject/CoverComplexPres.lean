module

public import RequestProject.CoverComplex
public import RequestProject.PresentationDictionary
public import RequestProject.NecessityAlgebraic

@[expose] public section

/-!
# The construction of the cover, phrased with `G = π₁(K)`

`RequestProject/CoverComplex.lean` builds the cover attached to a normal subgroup
`Ñ ◁ F` of the free group.  Section 2 of the paper phrases its requirements for normal
subgroups `N ◁ G = π₁(K) = F/R`.  This file bridges the two: for every normal subgroup
`N ◁ G` that is perfect and satisfies the requirements (2.2), the presentation complex has
a connected acyclic regular cover
(`FiniteChains.Comb.presComplex_hasAcyclicRegularCover_of_perfect`).

This is exactly the hypothesis `cover` of
`FiniteChains.hasAcyclicRegularCover_of_cellDataMod_pres`, now proved.
-/

namespace FiniteChains
namespace Comb

open MonoidAlgebra

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]
variable {J : Type u} [Fintype J] [DecidableEq J] (ρ : J → FreeGroup α)

/-- **The topological input `cover` of Section 2, proved.**  A perfect normal subgroup of
`G = π₁(K)` satisfying the requirements (2.2) yields a connected acyclic regular cover of
the presentation complex. -/
theorem presComplex_hasAcyclicRegularCover_of_perfect (N : Subgroup (PresGroup ρ)) [N.Normal]
    (hsat : ∀ v : J →₀ MonoidAlgebra ℤ (PresGroup ρ), FoxSat (foxMatrixPres ρ) v N)
    (hperf : ⁅N, N⁆ = N) :
    HasAcyclicRegularCover (presComplex ρ) := by
  classical
  set q := QuotientGroup.mk' (relSub ρ) with hq
  set Nsub := N.comap q with hNsub
  haveI : Nsub.Normal := inferInstance
  -- the relators lie in `Ñ`
  have hρ : ∀ j, ρ j ∈ Nsub := by
    intro j
    have hmem : ρ j ∈ relSub ρ := Subgroup.subset_normalClosure (Set.mem_range_self j)
    have : q (ρ j) = 1 := by
      simpa [hq, QuotientGroup.eq_one_iff] using hmem
    simp [hNsub, Subgroup.mem_comap, this]
  -- the requirements, transported to the free group
  have hsat' : ∀ v : J →₀ FreeGroupRing α, FoxSat (foxMatrix ρ) v Nsub := fun v =>
    foxSat_comap q N (foxMatrix ρ) (fun w => hsat w) v
  -- perfectness, transported to the free group
  have hperf' : Nsub ≤ relSub ρ ⊔ ⁅Nsub, Nsub⁆ := by
    have h := comap_le_ker_sup_commutator q (QuotientGroup.mk'_surjective (relSub ρ)) hperf
    rwa [hq, QuotientGroup.ker_mk'] at h
  exact presComplex_hasAcyclicRegularCover hρ hperf' hsat'

end Comb
end FiniteChains
