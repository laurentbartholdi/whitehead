import RequestProject.CutSurfaceSpine
import RequestProject.SurfaceBlockCollapse

/-!
# A nonempty instance of the chain collapse

The notion of a chain collapse of the truncated cube complex
(`FiniteChains.CollapseChain.IsChainCollapse` for the boundary matrix
`FiniteChains.cubeBdry`) is not vacuous: the collapse of Lemma 3.3 (ii) produced for the
barycentric subdivision of the boundary of the tetrahedron
(`FiniteChains.tetra_spine_collapse_barycentric`) is one.
-/

namespace FiniteChains

/-- An arbitrary linear order on the vertices of the subdivision, needed only to orient the
cells. -/
noncomputable local instance : LinearOrder tetraASC.Face := by
  classical
  exact linearOrderOfSTO (@WellOrderingRel tetraASC.Face)

/-- **The collapse of the truncated cube complex over the subdivided tetrahedron boundary is a
chain collapse.** -/
theorem tetra_exists_chainCollapse :
    ∃ lp : List (Cube tetraASC.Face × (Cube tetraASC.Face ⊕ Finset tetraASC.Face)),
      CollapseChain.IsChainCollapse (cubeBdry (V := tetraASC.Face)) lp := by
  obtain ⟨l, hl⟩ := tetra_spine_collapse_barycentric
  obtain ⟨lp, -, hchain⟩ := exists_chainCollapse (Finset.Subset.refl _) hl
  exact ⟨lp, hchain⟩

end FiniteChains
