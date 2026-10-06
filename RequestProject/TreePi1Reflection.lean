module

public import RequestProject.TreeChainTopological

@[expose] public section

/-! Triviality on pi1 reflects across a compatible spanning-tree
collapse, at every original vertex. Pending final Lean verification. -/

namespace FiniteChains.Comb.SpanningTree
universe u
variable {X Y : Complex2.{u}} {TX : SpanningTree X} {TY : SpanningTree Y}
  [DecidableEq (NonTree TX)] [DecidableEq (NonTree TY)]
  {h : Hom X Y} (hiff : ∀ e : X.E, TY.isTree (h.onE e) ↔ TX.isTree e)
  (hE : Function.Injective h.onE)

theorem pi1Trivial_of_pi1Trivial_presInclHom
    (hz : Pi1Trivial (presInclHom (nonTreeIncl hiff) (nonTreeIncl_injective hiff hE)
      (treeRel TX) (treeRel TY) h.onF (treeRel_onF hiff))) : Pi1Trivial h := by
  have hzero := (pi1Trivial_presInclHom_iff (ρ := treeRel TX) (σ := treeRel TY)
    (nonTreeIncl hiff) (nonTreeIncl_injective hiff hE) h.onF (treeRel_onF hiff)).mp hz
  intro a p hp
  have hword : wordClass TY (mapPath h p) = 1 := by
    change (QuotientGroup.mk (pathWord TY (mapPath h p)) : PresGroup (treeRel TY)) = 1
    rw [pathWord_mapPath hiff]
    exact hzero (QuotientGroup.mk (pathWord TX p))
  have hlo : loopOf TY (isPath_mapPath h hp) = 1 := by
    apply (pi1EquivPres TY).injective
    rw [map_one]
    exact (uvQ_conjPath (isPath_mapPath h hp)).trans hword
  have H : Htpy Y TY.root TY.root
      (conjPath TY (mapPath h p) (h.onV a) (h.onV a)) [] := Quotient.exact hlo
  have Hnil : Htpy Y TY.root TY.root
      (conjPath TY [] (h.onV a) (h.onV a)) [] := by
    simpa only [conjPath, List.append_nil] using htpy_append_revPath (TY.treePath_isPath (h.onV a))
  exact htpy_of_congr_append (TY.treePath_isPath (h.onV a))
    (isPath_revPath (TY.treePath_isPath (h.onV a)))
    (isPath_mapPath h hp) rfl (H.trans Hnil.symm)

end FiniteChains.Comb.SpanningTree
