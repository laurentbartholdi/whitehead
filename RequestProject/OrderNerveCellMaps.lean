module

public import RequestProject.OrderPosetCoverThree
public import RequestProject.UnivCoverIncl
public import RequestProject.OrderNerveDecoding

@[expose] public section

/-! Naturality of actual cellular order chains in the full nerve. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

theorem ordNerveChain2_chain2 (f : P → Q) (hf : Monotone f) (c : OrdTri P →₀ ℤ) :
    ordNerveChain2 (chain2 (orderCxMap f hf) c) = Nerve.cmap f (ordNerveChain2 c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, map_add]
  | single t n =>
      change ordNerveChain2 (Finsupp.mapDomain (orderCxMap f hf).onF
        (Finsupp.single t n)) = _
      rw [Finsupp.mapDomain_single]
      simp [ordNerveChain2, Nerve.cmap_of, orderCxMap]

/-- The full cellular three-boundary is natural under actual monotone maps. -/
theorem chain2_ordBoundary3 (f : P → Q) (hf : Monotone f) (c : OrdTet P →₀ ℤ) :
    chain2 (orderCxMap f hf) (ordBoundary3 c) =
      ordBoundary3 (Finsupp.mapDomain (ordTetMap f hf) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, Finsupp.mapDomain_add, map_add]
  | single t n =>
      rw [ordBoundary3, Finsupp.linearCombination_single, map_smul,
        Finsupp.mapDomain_single, ordBoundary3, Finsupp.linearCombination_single]
      congr 1
      exact ordTetMap_boundary f hf t

end FiniteChains.Comb
