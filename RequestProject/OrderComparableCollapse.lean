module

public import RequestProject.OrderDownwardCycleHomotopy
public import RequestProject.OrderNormalizationNaturality

@[expose] public section

/-! Actual strict cycle fillings from a componentwise downward collapse. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

theorem normalizedStrictChain2_zero_of_comparable_equal (g : P → P) (hg : Monotone g)
    (he : ∀ {a b : P}, a ≤ b → g a = g b) (c : StrictOrdTri P →₀ ℤ) :
    normalizedStrictChain2 g hg c = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add c d hc hd => rw [map_add, hc, hd, add_zero]
  | single t n =>
    rw [normalizedStrictChain2_single]
    have ht : g t.1.1 = g t.1.2.1 := he t.2.1.le
    simp [normalizeOrdTriangle, orderCxMap, strictOrderIncl, ht]

/-- A downward monotone map that identifies comparable vertices gives genuine finite
strict three-fillings of all strict two-cycles, even when the poset is disconnected. -/
theorem strict_cycle_boundary_of_downward_collapse (g : P → P) (hg : Monotone g)
    (hle : ∀ x, g x ≤ x) (he : ∀ {a b : P}, a ≤ b → g a = g b)
    (c : StrictOrdTri P →₀ ℤ) (hc : bdry2 (strictOrderCx P) c = 0) :
    ∃ y : StrictOrdTet P →₀ ℤ, strictOrdBoundary3 y = c := by
  let w := chain2 (strictOrderIncl P) c
  have hw : bdry2 (orderCx P) w = 0 := by
    rw [bdry2_chain2, hc, map_zero]
  obtain ⟨y, hy⟩ := ordCycle_downward_boundary g hg hle w hw
  have hn : normalizeOrdChain2 w = c := normalizeOrdChain2_inclusion c
  have hz : normalizeOrdChain2 (Finsupp.mapDomain (downwardOrdTriangleMap g hg) w) = 0 := by
    change normalizedStrictChain2 g hg c = 0
    exact normalizedStrictChain2_zero_of_comparable_equal g hg he c
  have h := congrArg normalizeOrdChain2 hy
  rw [normalizeOrdChain2_ordBoundary3, map_sub, hn, hz, sub_zero] at h
  exact ⟨normalizeOrdChain3 y, h⟩

end FiniteChains.Comb
