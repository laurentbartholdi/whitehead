import RequestProject.OrderNerveCellMaps
import RequestProject.NerveDegree

/-! Actual finite three-chains for downward order homotopies on two-cycles. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def downwardOrdTriangleMap (g : P → P) (hg : Monotone g) : OrdTri P → OrdTri P :=
  fun t => ⟨(g t.1.1, g t.1.2.1, g t.1.2.2), hg t.2.1, hg t.2.2⟩

theorem ordCycle_downward_boundary (g : P → P) (hg : Monotone g)
    (hgle : ∀ x, g x ≤ x) (c : OrdTri P →₀ ℤ)
    (hc : bdry2 (orderCx P) c = 0) :
    ∃ y : OrdTet P →₀ ℤ, ordBoundary3 y = c -
      Finsupp.mapDomain (downwardOrdTriangleMap g hg) c := by
  let p := Nerve.prism g id (ordNerveChain2 c)
  have hp : p ∈ Nerve.Inc P :=
    Nerve.prism_mem_inc hg monotone_id hgle (ordNerveChain2_mem_inc c)
  have hd := (ordNerveChain2_cycle_iff c).mpr hc
  have hb : Nerve.bdry p = ordNerveChain2 c - Nerve.cmap g (ordNerveChain2 c) := by
    simpa [p, hd] using Nerve.bdry_prism_add_prism_bdry g id (ordNerveChain2 c)
  let b := Nerve.lengthProjection 4 p
  have hbi : b ∈ Nerve.Inc P := Nerve.lengthProjection_mem_inc _ hp
  have hdeg : Nerve.lengthProjection 4 b = b := Nerve.lengthProjection_idempotent _ _
  have hbdry : Nerve.bdry b = ordNerveChain2 c -
      Nerve.lengthProjection 3 (Nerve.cmap g (ordNerveChain2 c)) := by
    dsimp only [b]
    rw [← Nerve.lengthProjection_bdry, hb, map_sub, ordNerveChain2_lengthProjection]
  refine ⟨decodeOrdNerve3 b, ?_⟩
  apply ordNerveChain2_injective
  rw [ordNerveChain2_ordBoundary3, ordNerveChain3_decode hbi, hdeg, map_sub, hbdry]
  rw [← ordNerveChain2_chain2 g hg, ordNerveChain2_lengthProjection]
  rfl

end FiniteChains.Comb
