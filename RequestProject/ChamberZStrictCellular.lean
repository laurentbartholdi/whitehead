import RequestProject.ChamberZCellular
import RequestProject.OrderNormalizationSupport

/-! Relative generation using genuine nondegenerate chamber flags. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {M : CayGroup A → Prop} {att : NeSpx A →o X}

/-- Every nondegenerate modified-chamber two-cycle is a base-supported cycle
plus the boundary of a finite chain of nondegenerate three-flags. -/
theorem exists_base_strict_cellular_cycle [Nonempty X]
    (z : StrictOrdTri (Zpos A X M att) →₀ ℤ)
    (hz : Comb.bdry2 (strictOrderCx (Zpos A X M att)) z = 0) :
    ∃ c : StrictOrdTri (Zpos A X M att) →₀ ℤ,
      (∀ t ∈ c.support, InZBase t.1.1 ∧ InZBase t.1.2.1 ∧ InZBase t.1.2.2) ∧
      Comb.bdry2 (strictOrderCx (Zpos A X M att)) c = 0 ∧
      ∃ y : StrictOrdTet (Zpos A X M att) →₀ ℤ, z = c + strictOrdBoundary3 y := by
  let w := chain2 (strictOrderIncl (Zpos A X M att)) z
  have hw : Comb.bdry2 (orderCx (Zpos A X M att)) w = 0 := by
    rw [bdry2_chain2, hz, map_zero]
  obtain ⟨c, hc, hcycle, y, hy⟩ := exists_base_cellular_cycle w hw
  refine ⟨normalizeOrdChain2 c, ?_, normalizeOrdChain2_cycle c hcycle,
    normalizeOrdChain3 y, ?_⟩
  · intro t ht
    obtain ⟨a, ha, he⟩ := normalizeOrdChain2_support c t ht
    have hbase := (Finsupp.mem_supported ℤ c).mp hc ha
    change InZBase a.1.1 ∧ InZBase a.1.2.1 ∧ InZBase a.1.2.2 at hbase
    rwa [he] at hbase
  · have hn : normalizeOrdChain2 w = z := normalizeOrdChain2_inclusion z
    rw [← hn, hy, map_add, normalizeOrdChain2_ordBoundary3]

end FiniteChains.Davis
