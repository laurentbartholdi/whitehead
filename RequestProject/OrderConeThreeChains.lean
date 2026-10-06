import RequestProject.OrderConeChains
import RequestProject.OrderNerveCellMaps

/-! Actual tetrahedron cone chains and their cellular boundary. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
  (f : P → Q) (hf : Monotone f) (c : Q) (hc : ∀ x, c ≤ f x)

def coneTriangleTetrahedron (t : OrdTri P) : OrdTet Q :=
  ⟨(c, f t.1.1, f t.1.2.1, f t.1.2.2), hc _, hf t.2.1, hf t.2.2⟩

noncomputable def coneTriangleChain : (OrdTri P →₀ ℤ) →ₗ[ℤ] (OrdTet Q →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (coneTriangleTetrahedron f hf c hc)

/-- Coning an actual triangle has its mapped face minus the cone of its edge boundary. -/
theorem coneTriangleTetrahedron_boundary (t : OrdTri P) :
    ordTetBoundary (coneTriangleTetrahedron f hf c hc t) =
      Finsupp.single ((orderCxMap f hf).onF t) 1 -
        coneEdgeChain f hf c hc (FiniteChains.Comb.bdry2 (orderCx P) (Finsupp.single t 1)) := by
  rw [bdry2_single (X := orderCx P)]
  simp only [one_smul]
  simp only [pathChain, orderCx, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp [map_add, map_sub, map_smul, Finsupp.linearCombination_single, ordTetBoundary, coneTriangleTetrahedron, coneEdgeChain, coneEdgeTriangle,
    bdry2, orderCx, orderCxMap, pathChain, smul_add]
  rw (config := { transparency := .default }) [map_add, map_add, map_neg]
  rw (config := { transparency := .default }) [Finsupp.linearCombination_single,
    Finsupp.linearCombination_single, Finsupp.linearCombination_single]
  simp only [one_smul]
  let a : OrdTri Q := (orderCxMap f hf).onF t
  let b : OrdTri Q := coneEdgeTriangle f hf c hc ⟨t.val.2, t.property.2⟩
  let d : OrdTri Q := coneEdgeTriangle f hf c hc ⟨(t.val.1, t.val.2.1), t.property.1⟩
  let e : OrdTri Q := coneEdgeTriangle f hf c hc ⟨(t.val.1, t.val.2.2), t.property.1.trans t.property.2⟩
  have h (a b e d : OrdTri Q →₀ ℤ) : a - b + e - d = a - (d + (b + -e)) := by
    abel
  exact h (Finsupp.single a 1) (Finsupp.single b 1)
    (Finsupp.single e 1) (Finsupp.single d 1)

/-- The cone identity retains all genuine cellular three-boundaries. -/
theorem coneTriangleChain_boundary (z : OrdTri P →₀ ℤ) :
    ordBoundary3 (coneTriangleChain f hf c hc z) = chain2 (orderCxMap f hf) z -
      coneEdgeChain f hf c hc (FiniteChains.Comb.bdry2 (orderCx P) z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add, map_add]; abel
  | single t n =>
      change ordBoundary3 (Finsupp.mapDomain (coneTriangleTetrahedron f hf c hc)
        (Finsupp.single t n)) = _
      rw [Finsupp.mapDomain_single, ordBoundary3, Finsupp.linearCombination_single,
        coneTriangleTetrahedron_boundary]
      change n • (Finsupp.single ((orderCxMap f hf).onF t) 1 - _) =
        Finsupp.mapDomain (orderCxMap f hf).onF (Finsupp.single t n) - _
      rw [Finsupp.mapDomain_single, smul_sub, Finsupp.smul_single, smul_eq_mul, mul_one,
        bdry2_single, map_smul]
      simp [map_add, map_sub, map_smul, Finsupp.linearCombination_single, bdry2]

theorem coneTriangleChain_cycle_boundary (z : OrdTri P →₀ ℤ)
    (hz : FiniteChains.Comb.bdry2 (orderCx P) z = 0) :
    ordBoundary3 (coneTriangleChain f hf c hc z) = chain2 (orderCxMap f hf) z := by
  rw [coneTriangleChain_boundary, hz, map_zero, sub_zero]

end FiniteChains.Comb
