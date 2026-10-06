import RequestProject.CubeMedianGraph
import RequestProject.CollapseChainMap

/-!
# The CAT(0) input feeds the collapse: cycles of a collapsed median cube complex

`RequestProject/CubeMedianGraph.lean` proves the chain-level Cartan–Hadamard step for a cube
complex whose one-skeleton is a median graph — the combinatorial form of the CAT(0) input of
the paper: every two-cycle of the cellular chain complex is the boundary of a three-chain
(`FiniteChains.MedianGraph.exists_d₃_eq`).

`RequestProject/CollapseChainMap.lean` provides the chain map of a collapse and shows that a
two-cycle of a collapsed complex is a combination of the boundaries of the surviving
three-cells.

This file joins the two: **in a median cube complex, after a collapse removing all
three-cells outside a set `E`, every two-cycle of the spine is a combination of the collapsed
boundaries of the cells of `E`.**  With `E` the set of lifts of the cone cell, this is the
asphericity of the cone model in the form used by the capping argument for (B3).
-/

namespace FiniteChains
namespace MedianGraph

universe u

variable {Vx : Type u} (G : MedianGraph Vx) [LinearOrder Vx]

/-- The boundary matrix of the three-cells of the cube complex of a median graph. -/
noncomputable def cubeBdryMatrix : (G.toDescCubeStr).CbC → (G.toDescCubeStr).SqC → ℤ :=
  CollapseChain.ofLinearMap (G.toDescCubeStr).d₃

/-- **The two-cycles of a collapsed median cube complex.**  If a chain collapse removes every
three-cell outside `E`, then a two-cycle supported on the surviving squares is a combination
of the collapsed boundaries of the three-cells of `E`.  The hypothesis that every two-cycle
bounds is the theorem `FiniteChains.MedianGraph.exists_d₃_eq`, i.e. the CAT(0) input. -/
theorem exists_sum_collapsed_bdry
    {l : List ((G.toDescCubeStr).CbC × (G.toDescCubeStr).SqC)}
    (hl : CollapseChain.IsChainCollapse (cubeBdryMatrix G) l)
    (E : Set (G.toDescCubeStr).CbC) (hcoll : ∀ t, t ∉ E → ∃ f, (t, f) ∈ l)
    (z : (G.toDescCubeStr).SqC →₀ ℤ) (hz : (G.toDescCubeStr).d₂ z = 0)
    (hspine : ∀ p ∈ l, z p.2 = 0) :
    ∃ (s : Finset (G.toDescCubeStr).CbC) (c : (G.toDescCubeStr).CbC → ℤ),
      (∀ t ∈ s, t ∈ E) ∧
        ∀ g, z g = ∑ t ∈ s, c t * CollapseChain.cmap (cubeBdryMatrix G) l
          (cubeBdryMatrix G t) g := by
  classical
  refine CollapseChain.exists_sum_bdry_of_cycles_bound hl E
    (fun x => ∃ w : (G.toDescCubeStr).SqC →₀ ℤ, ⇑w = x ∧ (G.toDescCubeStr).d₂ w = 0)
    ?_ hcoll ⟨z, rfl, hz⟩ hspine
  rintro x ⟨w, rfl, hw⟩
  exact CollapseChain.exists_sum_of_exists_preimage (G.toDescCubeStr).d₃
    (fun y => (G.toDescCubeStr).d₂ y = 0) (fun y hy => G.exists_d₃_eq y hy) w hw

end MedianGraph
end FiniteChains
