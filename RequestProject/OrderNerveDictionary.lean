import RequestProject.OrderNormalizationHomotopy
import RequestProject.NervePrism

/-! The actual cellular boundary maps in degrees two and three agree with the full nerve. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

noncomputable def ordNerveChain1 : (OrdEdge P →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  Finsupp.linearCombination ℤ (fun e => FreeAbelianGroup.of [e.1.1, e.1.2])

noncomputable def ordNerveChain2 : (OrdTri P →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  Finsupp.linearCombination ℤ (fun t => FreeAbelianGroup.of [t.1.1, t.1.2.1, t.1.2.2])

noncomputable def ordNerveChain3 : (OrdTet P →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  Finsupp.linearCombination ℤ (fun t =>
    FreeAbelianGroup.of [t.1.1, t.1.2.1, t.1.2.2.1, t.1.2.2.2])

/-- A triangle's attaching edge chain is its alternating simplicial boundary. -/
theorem ordNerveChain1_bdry2 (c : OrdTri P →₀ ℤ) :
    ordNerveChain1 (bdry2 (orderCx P) c) = Nerve.bdry (ordNerveChain2 c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single t n =>
    rw [bdry2_single]
    simp [ordNerveChain1, ordNerveChain2, pathChain, orderCx, Nerve.bdryOn,
      Nerve.consMap_of, smul_add, smul_sub]
    abel

/-- The cellular three-boundary is exactly the full nerve three-boundary. -/
theorem ordNerveChain2_ordBoundary3 (c : OrdTet P →₀ ℤ) :
    ordNerveChain2 (ordBoundary3 c) = Nerve.bdry (ordNerveChain3 c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single t n =>
    simp [ordNerveChain2, ordNerveChain3, ordBoundary3, ordTetBoundary,
      Nerve.bdryOn, Nerve.consMap_of, smul_add, smul_sub]
    abel

/-- The normalized image of every weak two-cycle represents the same full-nerve class. -/
theorem ordNerve_normalization_cycle (c : OrdTri P →₀ ℤ)
    (hc : bdry2 (orderCx P) c = 0) :
    ordNerveChain2 c - ordNerveChain2 (ordStrictInclusion2 (normalizeOrdChain2 c)) =
      Nerve.bdry (ordNerveChain3 (ordNormalizationHomotopy2 c)) := by
  rw [← map_sub, ordNormalization_cycle_boundary c hc, ordNerveChain2_ordBoundary3]

end FiniteChains.Comb
