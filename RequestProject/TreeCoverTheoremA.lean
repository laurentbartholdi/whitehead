import RequestProject.TreeCoverAcyclic
import RequestProject.CoverComplexPres
import RequestProject.PresentationNecessity
import RequestProject.PresChainTopological

/-!
# `(1) ⇒ (2)` of Theorem A for an arbitrary finite connected two-complex

Everything in Section 2 of the paper is carried out on the two-complex of a finite
presentation.  A general connected two-complex `K` becomes one after collapsing a spanning
tree `T` of its one-skeleton: the resulting presentation is `⟨E ∖ T | the attaching words⟩`
(`FiniteChains.Comb.SpanningTree.treeRel`), and its group is `π₁(K)`
(`FiniteChains.Comb.SpanningTree.pi1_mulEquiv_presGroup`).

`RequestProject/TreeCover.lean` and `RequestProject/TreeCoverAcyclic.lean` build the cover of
`K` itself attached to a normal subgroup `N` of the free group on the non-tree edges and prove
that it is a connected regular covering which is acyclic whenever the corresponding cover of
the collapsed presentation complex is.  Combining this with Section 2 gives Theorem A's
implication for `K`:

* `FiniteChains.Comb.SpanningTree.hasAcyclicRegularCover_of_foxSat` — a perfect normal subgroup
  satisfying the requirements (2.2) of the paper yields a connected acyclic regular cover of
  `K` (the topological input of Section 2, for a general two-complex);
* `FiniteChains.Comb.SpanningTree.hasAcyclicRegularCover_of_perfect` — the same with the
  subgroup taken inside `π₁(K)`;
* `FiniteChains.Comb.SpanningTree.hasAcyclicRegularCover_of_cellChains` — the cell-level form
  of condition (1) of Theorem A suffices;
* `FiniteChains.Comb.SpanningTree.hasAcyclicRegularCover_of_topChains` — **`(1) ⇒ (2)` of
  Theorem A for a finite connected two-complex**: if over the collapsed presentation complex
  there are chains of presentation complexes of every length whose inclusions are zero on `π₂`,
  then `K` has a connected acyclic regular cover.
-/

namespace FiniteChains
namespace Comb
namespace SpanningTree

universe u

variable {K : Complex2.{u}} (T : SpanningTree K)
variable [Fintype (NonTree T)] [DecidableEq (NonTree T)] [Fintype K.F] [DecidableEq K.F]

/-- **The topological input of Section 2, for a general two-complex.**  A normal subgroup of
the free group on the non-tree edges which contains the relators, is perfect modulo them and
satisfies the requirements (2.2) yields a connected acyclic regular cover of `K`. -/
theorem hasAcyclicRegularCover_of_foxSat (N : Subgroup (FreeGroup (NonTree T))) [N.Normal]
    (hN : ∀ f, treeRel T f ∈ N)
    (hperf : N ≤ Subgroup.normalClosure (Set.range (treeRel T)) ⊔ ⁅N, N⁆)
    (hsat : ∀ v : K.F →₀ FreeGroupRing (NonTree T), FoxSat (foxMatrix (treeRel T)) v N) :
    HasAcyclicRegularCover K :=
  ⟨treeCover T N hN, CovQ T N, inferInstance, treeCoverProj T N hN, treeCoverDeck T N hN,
    treeCoverProj_isCovering T N hN, treeCoverProj_isRegular T N hN,
    treeCover_isConnected T N hN,
    treeCover_isAcyclic (T := T) (N := N) (hN := hN)
      (coverComplex_isAcyclic hN hperf
        (bdry2_injective_of_foxSat N (treeRel T) hsat))⟩

/-- The same, with the subgroup taken inside the fundamental group `π₁(K)` of `K`, which the
collapse presents. -/
theorem hasAcyclicRegularCover_of_perfect (M : Subgroup (PresGroup (treeRel T))) [M.Normal]
    (hsat : ∀ v : K.F →₀ MonoidAlgebra ℤ (PresGroup (treeRel T)),
      FoxSat (foxMatrixPres (treeRel T)) v M)
    (hperf : ⁅M, M⁆ = M) :
    HasAcyclicRegularCover K := by
  classical
  set q := QuotientGroup.mk' (relSub (treeRel T)) with hq
  set Nsub := M.comap q with hNsub
  haveI : Nsub.Normal := inferInstance
  have hρ : ∀ f, treeRel T f ∈ Nsub := by
    intro f
    have hmem : treeRel T f ∈ relSub (treeRel T) :=
      Subgroup.subset_normalClosure (Set.mem_range_self f)
    have hone : q (treeRel T f) = 1 := by
      simpa [hq, QuotientGroup.eq_one_iff] using hmem
    simp [hNsub, Subgroup.mem_comap, hone]
  have hsat' : ∀ v : K.F →₀ FreeGroupRing (NonTree T),
      FoxSat (foxMatrix (treeRel T)) v Nsub := fun v =>
    foxSat_comap q M (foxMatrix (treeRel T)) (fun w => hsat w) v
  have hperf' : Nsub ≤ relSub (treeRel T) ⊔ ⁅Nsub, Nsub⁆ := by
    have h := comap_le_ker_sup_commutator q
      (QuotientGroup.mk'_surjective (relSub (treeRel T))) hperf
    rwa [hq, QuotientGroup.ker_mk'] at h
  exact hasAcyclicRegularCover_of_foxSat T Nsub hρ hperf' hsat'

/-- **Condition (1) of Theorem A at cell level suffices**, for a general finite connected
two-complex: the chains are taken over the presentation complex of the collapse. -/
theorem hasAcyclicRegularCover_of_cellChains
    (hchains : HasCellChainsLift (foxMatrixPres (treeRel T))) :
    HasAcyclicRegularCover K := by
  obtain ⟨M, hMnormal, -, hint, hperf⟩ :=
    exists_perfect_normal_foxSatMod hchains (foxBoundaryPres_finite (treeRel T))
      (foxMatrixPres_col_finite (treeRel T))
      (fun M _ hmod => isMulTorsionFree_of_foxSatMod_pres (treeRel T) M hmod)
  haveI := hMnormal
  exact hasAcyclicRegularCover_of_perfect T M hint hperf

/-- **`(1) ⇒ (2)` of Theorem A for a finite connected two-complex.**  Let `T` be a spanning
tree of `K` and let `⟨E ∖ T | r⟩` be the presentation obtained by collapsing it.  If over that
presentation complex there are chains `X₀ ⊂ X₁ ⊂ ⋯ ⊂ Xₙ` of presentation complexes of every
length whose inclusions are zero on `π₂`, then `K` has a connected acyclic regular cover. -/
theorem hasAcyclicRegularCover_of_topChains
    (hchains : ∀ n : ℕ, Nonempty (PresChainTop (treeRel T) n)) :
    HasAcyclicRegularCover K :=
  hasAcyclicRegularCover_of_cellChains T
    (hasCellChainsLift_of_presChains (treeRel T)
      (fun n => (hchains n).map PresChainTop.toPresChain))

end SpanningTree
end Comb
end FiniteChains
