import RequestProject.TreeChainTopological

/-! The reverse direction of the spanning-tree comparison for actual
cellular inclusions. It lets a relative presentation extension be moved
back to the original graph without losing its vanishing on pi2.
 -/

namespace FiniteChains.Comb.SpanningTree
universe u
variable {X Y : Complex2.{u}} {TX : SpanningTree X} {TY : SpanningTree Y}
  [DecidableEq (NonTree TX)] [DecidableEq (NonTree TY)]
  {h : Hom X Y} (hiff : ∀ e : X.E, TY.isTree (h.onE e) ↔ TX.isTree e)
  (hE : Function.Injective h.onE)

theorem zeroPi2_of_zeroPi2_presInclHom
    (hz : ZeroPi2 (presInclHom (nonTreeIncl hiff) (nonTreeIncl_injective hiff hE)
      (treeRel TX) (treeRel TY) h.onF (treeRel_onF hiff))) : ZeroPi2 h := by
  classical
  have hzero := (zeroPi2_presInclHom_iff (ρ := treeRel TX) (σ := treeRel TY)
    (nonTreeIncl hiff) (nonTreeIncl_injective hiff hE) h.onF (treeRel_onF hiff)).mp hz
  intro x z hz
  have hcycle := (mem_pi2_iff_bdry2_univCover TX z).mp hz
  have hinj : Function.Injective (chain2 (treeUnivHom TY (h.onV x))) :=
    Finsupp.mapDomain_injective (uvFace_injective TY)
  apply hinj
  rw [map_zero, chain2_treeUnivHom_square hiff hE]
  exact hzero _ hcycle

theorem zeroPi2_iff_zeroPi2_presInclHom :
    ZeroPi2 h ↔ ZeroPi2 (presInclHom (nonTreeIncl hiff) (nonTreeIncl_injective hiff hE)
      (treeRel TX) (treeRel TY) h.onF (treeRel_onF hiff)) :=
  ⟨zeroPi2_presInclHom_of_zeroPi2 hiff hE,
    zeroPi2_of_zeroPi2_presInclHom hiff hE⟩

end FiniteChains.Comb.SpanningTree
