import RequestProject.NecessityAlgebraicMod
import RequestProject.CoverComplexPres
import RequestProject.PresentationConsistency

/-!
# `(1) ⇒ (2)` of Theorem A for a presented complex, with the cover constructed

This file assembles the two halves developed so far.

* `RequestProject/NecessityAlgebraicMod.lean` derives from the cell data of the chains a
  perfect normal subgroup `N ◁ G = π₁(K)` satisfying all the requirements (2.2); for a
  presented complex the torsion freeness it needs is the theorem
  `FiniteChains.isMulTorsionFree_of_foxSatMod_pres`.
* `RequestProject/CoverComplex.lean` constructs, from such an `N`, the cover `K_N` as an
  honest combinatorial two-complex and proves that it is a connected acyclic regular cover
  of the presentation complex.

The conclusion, `FiniteChains.presComplex_hasAcyclicRegularCover_of_cellChains`, is the
implication `(1) ⇒ (2)` of Theorem A for the two-complex of a finite presentation: the
single remaining hypothesis is `HasCellChainsLift`, the cell-level description of the
chains of condition (1) (the cells of the stages, their Fox boundary matrices, the
vanishing of the inclusions on `π₂ = ker ∂₂` at chain level and the lifting of cycles
modulo `m`).  Everything else — the whole of Section 2, the Hurewicz dictionary, the
universal-coefficient input and the construction of the acyclic regular cover — is proved.
-/

namespace FiniteChains

open MonoidAlgebra

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]
variable {J : Type u} [Fintype J] [DecidableEq J]

/-- **`(1) ⇒ (2)` of Theorem A for the two-complex of a finite presentation.**  If the
chains of condition (1) exist for every length — at the level of the cell data of their
stages — then the presentation complex has a connected acyclic regular cover. -/
theorem presComplex_hasAcyclicRegularCover_of_cellChains (ρ : J → FreeGroup α)
    (hchains : HasCellChainsLift (foxMatrixPres ρ)) :
    Comb.HasAcyclicRegularCover (Comb.presComplex ρ) := by
  obtain ⟨N, hNnormal, -, hint, hperf⟩ :=
    exists_perfect_normal_foxSatMod hchains (foxBoundaryPres_finite ρ)
      (foxMatrixPres_col_finite ρ)
      (fun N _ hmod => isMulTorsionFree_of_foxSatMod_pres ρ N hmod)
  haveI := hNnormal
  exact Comb.presComplex_hasAcyclicRegularCover_of_perfect ρ N hint hperf

/-! ### The hypothesis is satisfiable -/

/-- The cell data required above does occur: for the presentation `⟨x | x⟩` the chains of
every length exist at cell level, with the lifting of cycles modulo every `m`. -/
theorem hasCellChainsLift_presRho : HasCellChainsLift (foxMatrixPres presRho) := by
  intro n
  obtain ⟨h, hlift⟩ := exists_chainInput_presRho n
  exact ⟨_, _, _, _, h, hlift⟩

/-- Consequently the theorem above is not vacuous: the complex of the presentation
`⟨x | x⟩` has a connected acyclic regular cover. -/
theorem presComplex_presRho_hasAcyclicRegularCover :
    Comb.HasAcyclicRegularCover (Comb.presComplex presRho) :=
  presComplex_hasAcyclicRegularCover_of_cellChains presRho hasCellChainsLift_presRho

end FiniteChains
