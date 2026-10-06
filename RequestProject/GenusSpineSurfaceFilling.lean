module

public import RequestProject.GenusCollapseIteration
public import RequestProject.SurfaceCellularCycle

@[expose] public section

/-! The canonical surface relation fills in the actual surviving genus spine. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem spineMarkedLoop_hfilling :
    commWord (fun x : Fin q × Bool => Pi1.mk (spineMarkedLoop q x))
      (finitePairs q) = 1 := by
  apply genusSpineToOld_pi1_injective q
  rw [map_one, map_commWord]
  rw [commWord_congr (spineMarkedLoop_toOld_class q)]
  have h := congrArg (pi1Map (surfCx (cmpRel (GenusVertex q))) (gBase q))
    (finite_hfilling q)
  rw [map_one, map_commWord] at h
  exact h

theorem spineSurfacePath_nullhomotopic :
    Htpy (genusSpineCx q) (spineBase q) (spineBase q)
      (surfacePath (spineMarkedLoop q) (finitePairs q)) [] :=
  surfacePath_nullhomotopic _ _ (spineMarkedLoop_hfilling q)

theorem spineSurfacePath_chain_zero :
    pathChain (surfacePath (spineMarkedLoop q) (finitePairs q)) = 0 :=
  surfacePath_chain _ _

end FiniteChains.Davis.Genus
