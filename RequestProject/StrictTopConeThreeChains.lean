import RequestProject.StrictTopConeChains

/-! Genuine strict tetrahedron fans, with their alternating boundary. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
  (f : P → Q) (hf : StrictMono f) (c : Q) (hc : ∀ x, f x < c)

def strictTopConeTriangleTetrahedron (t : (strictOrderCx P).F) : StrictOrdTet Q :=
  ⟨(f t.1.1, f t.1.2.1, f t.1.2.2, c), hf t.2.1, hf t.2.2, hc _⟩

noncomputable def strictTopConeTriangleChain : ((strictOrderCx P).F →₀ ℤ) →ₗ[ℤ] (StrictOrdTet Q →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (strictTopConeTriangleTetrahedron f hf c hc)

/-- The sign of the upper cone is fixed by the actual alternating tetrahedron boundary. -/
theorem strictTopConeTriangleTetrahedron_boundary (t : (strictOrderCx P).F) :
    strictOrdTetBoundary (strictTopConeTriangleTetrahedron f hf c hc t) =
      strictTopConeEdgeChain f hf c hc (bdry2 (strictOrderCx P) (Finsupp.single t 1)) -
        Finsupp.single ((strictOrderCxMap f hf).onF t) 1 := by
  rw [bdry2_single (X := strictOrderCx P)]
  simp only [one_smul]
  simp only [pathChain, strictOrderCx, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp [map_add, map_neg, Finsupp.linearCombination_single, strictOrdTetBoundary, strictTopConeTriangleTetrahedron, strictTopConeEdgeChain, strictTopConeEdgeTriangle,
    bdry2, strictOrderCx, strictOrderCxMap, pathChain]
  rw (config := { transparency := .default }) [map_add, map_add, map_neg]
  rw (config := { transparency := .default }) [Finsupp.linearCombination_single,
    Finsupp.linearCombination_single, Finsupp.linearCombination_single]
  simp only [one_smul]
  abel

theorem strictTopConeTriangleChain_boundary (z : (strictOrderCx P).F →₀ ℤ) :
    strictOrdBoundary3 (strictTopConeTriangleChain f hf c hc z) =
      strictTopConeEdgeChain f hf c hc (bdry2 (strictOrderCx P) z) - chain2 (strictOrderCxMap f hf) z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add, map_add]; abel
  | single t n =>
      change strictOrdBoundary3 (Finsupp.mapDomain (strictTopConeTriangleTetrahedron f hf c hc)
        (Finsupp.single t n)) = _
      rw [Finsupp.mapDomain_single, strictOrdBoundary3, Finsupp.linearCombination_single,
        strictTopConeTriangleTetrahedron_boundary, smul_sub]
      change _ = _ - Finsupp.mapDomain (strictOrderCxMap f hf).onF (Finsupp.single t n)
      rw [Finsupp.mapDomain_single]
      simp [bdry2]

/-- Negating the upper cone fills an actual mapped two-cycle. -/
theorem strictTopConeTriangleChain_cycle_boundary (z : (strictOrderCx P).F →₀ ℤ)
    (hz : bdry2 (strictOrderCx P) z = 0) :
    strictOrdBoundary3 (-strictTopConeTriangleChain f hf c hc z) = chain2 (strictOrderCxMap f hf) z := by
  rw [map_neg, strictTopConeTriangleChain_boundary, hz, map_zero, zero_sub, neg_neg]

/-- All tetrahedra in the strict upper fan have the specified top vertex. -/
theorem strictTopConeTriangleChain_eq_zero_off_top (z : (strictOrderCx P).F →₀ ℤ)
    (t : StrictOrdTet Q) (ht : t.1.2.2.2 ≠ c) :
    strictTopConeTriangleChain f hf c hc z t = 0 := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, Finsupp.add_apply, hz, hw, add_zero]
  | single a n =>
      have hne : strictTopConeTriangleTetrahedron f hf c hc a ≠ t := by
        intro h
        exact ht (congrArg (fun b : StrictOrdTet Q => b.1.2.2.2) h).symm
      change Finsupp.mapDomain (strictTopConeTriangleTetrahedron f hf c hc)
        (Finsupp.single a n) t = 0
      rw [Finsupp.mapDomain_single]
      simp [hne]

end FiniteChains.Comb
