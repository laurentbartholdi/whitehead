module

public import RequestProject.TreeCoverAcyclic
public import RequestProject.PresentationChainFinsupp

@[expose] public section

/-! Necessity cover construction after spanning-tree collapse, for arbitrary cell sets. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.SpanningTree
universe u
variable {K : Complex2.{u}} (T : SpanningTree K) [DecidableEq (NonTree T)]

theorem fs_hasAcyclicRegularCover_of_perfect
    (H : Subgroup (PresGroup (treeRel T))) [H.Normal]
    (hsat : ∀ v : K.F →₀ MonoidAlgebra ℤ (PresGroup (treeRel T)), FoxSat (foxMatrixPres (treeRel T)) v H)
    (hperf : ⁅H, H⁆ = H) : HasAcyclicRegularCover K := by
  let q := QuotientGroup.mk' (relSub (treeRel T))
  let Nt := H.comap q
  have hR : relSub (treeRel T) ≤ Nt := by
    intro r hr
    change q r ∈ H
    have he : q r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
    rw [he]
    exact H.one_mem
  have hNeq : presSub (treeRel T) Nt = H :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) H
  have hm : ∀ v : K.F →₀ MonoidAlgebra ℤ (PresGroup (treeRel T)),
      FoxSat (foxMatrixPres (treeRel T)) v (presSub (treeRel T) Nt) := by
    rw [hNeq]
    exact hsat
  have hp : Nt ≤ Subgroup.normalClosure (Set.range (treeRel T)) ⊔ ⁅Nt, Nt⁆ := by
    have he := comap_le_ker_sup_commutator q (QuotientGroup.mk'_surjective _) hperf
    simpa only [q, Nt, QuotientGroup.ker_mk', relSub] using he
  have hρ : ∀ f, treeRel T f ∈ Nt :=
    fun f => hR (Subgroup.subset_normalClosure (Set.mem_range_self f))
  exact ⟨treeCover T Nt hρ, CovQ T Nt, inferInstance,
    treeCoverProj T Nt hρ, treeCoverDeck T Nt hρ,
    treeCoverProj_isCovering T Nt hρ, treeCoverProj_isRegular T Nt hρ,
    treeCover_isConnected T Nt hρ,
    treeCover_isAcyclic (T := T) (N := Nt) (hN := hρ)
      (fs_coverComplex_isAcyclic Nt (treeRel T) hρ hp
        (fs_injective_boundary_of_foxSat (treeRel T) Nt hR hm))⟩

theorem fs_hasAcyclicRegularCover_of_cellChains
    (hchains : HasCellChainsLift (foxMatrixPres (treeRel T))) :
    HasAcyclicRegularCover K := by
  obtain ⟨H, hnormal, _, hs, hp⟩ :=
    fs_exists_perfect_normal_of_cellChains (treeRel T) hchains
  letI := hnormal
  exact fs_hasAcyclicRegularCover_of_perfect T H hs hp

theorem fs_hasAcyclicRegularCover_of_presChains
    (hchains : ∀ n, Nonempty (PresChainFS (treeRel T) n)) :
    HasAcyclicRegularCover K :=
  fs_hasAcyclicRegularCover_of_cellChains T
    (hasCellChainsLift_of_presChainsFS (treeRel T) hchains)

end FiniteChains.Comb.SpanningTree
