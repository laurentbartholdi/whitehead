import RequestProject.OrderConeThreeChains

/-! Actual upper-cone triangle and tetrahedron chains for cell subdivisions. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
  (f : P → Q) (hf : Monotone f) (c : Q) (hc : ∀ x, f x ≤ c)

def topConeEdgeTriangle (e : (orderCx P).E) : (orderCx Q).F :=
  ⟨(f e.1.1, f e.1.2, c), hf e.2, hc _⟩

noncomputable def topConeEdgeChain : ((orderCx P).E →₀ ℤ) →ₗ[ℤ] ((orderCx Q).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun e => Finsupp.single (topConeEdgeTriangle f hf c hc e) 1)

def topConeRadialEdge (x : P) : (orderCx Q).E := ⟨(f x, c), hc x⟩

noncomputable def topConeRadialChain : (P →₀ ℤ) →ₗ[ℤ] ((orderCx Q).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => Finsupp.single (topConeRadialEdge f c hc x) 1)

theorem topConeEdgeTriangle_boundary (e : (orderCx P).E) :
    bdry2 (orderCx Q) (Finsupp.single (topConeEdgeTriangle f hf c hc e) 1) =
      Finsupp.single ((orderCxMap f hf).onE e) 1 +
        Finsupp.single (topConeRadialEdge f c hc e.1.2) 1 -
        Finsupp.single (topConeRadialEdge f c hc e.1.1) 1 := by
  simp [bdry2, topConeEdgeTriangle, topConeRadialEdge, orderCx, orderCxMap, pathChain]
  abel

/-- The upper triangle cone commutes with the edge boundary, with its radial correction. -/
theorem topConeEdgeChain_boundary (z : (orderCx P).E →₀ ℤ) :
    bdry2 (orderCx Q) (topConeEdgeChain f hf c hc z) =
      chain1 (orderCxMap f hf) z + topConeRadialChain f c hc (bdry1 (orderCx P) z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => rw (config := { transparency := .default }) [map_add, map_add, hz, hw, map_add, map_add, map_add]; abel
  | single e n =>
      rw (config := { transparency := .default }) [topConeEdgeChain, Finsupp.linearCombination_single, map_smul,
        topConeEdgeTriangle_boundary]
      change _ = Finsupp.mapDomain (orderCxMap f hf).onE (Finsupp.single e n) + _
      rw (config := { transparency := .default }) [Finsupp.mapDomain_single]
      simp [topConeRadialChain, bdry1, smul_add, smul_sub]
      abel

theorem topConeEdgeChain_cycle_boundary (z : (orderCx P).E →₀ ℤ)
    (hz : bdry1 (orderCx P) z = 0) :
    bdry2 (orderCx Q) (topConeEdgeChain f hf c hc z) = chain1 (orderCxMap f hf) z := by
  rw (config := { transparency := .default }) [topConeEdgeChain_boundary, hz, map_zero, add_zero]

def topConeTriangleTetrahedron (t : OrdTri P) : OrdTet Q :=
  ⟨(f t.1.1, f t.1.2.1, f t.1.2.2, c), hf t.2.1, hf t.2.2, hc _⟩

noncomputable def topConeTriangleChain : (OrdTri P →₀ ℤ) →ₗ[ℤ] (OrdTet Q →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (topConeTriangleTetrahedron f hf c hc)

/-- The sign of the upper cone is fixed by the actual alternating tetrahedron boundary. -/
theorem topConeTriangleTetrahedron_boundary (t : OrdTri P) :
    ordTetBoundary (topConeTriangleTetrahedron f hf c hc t) =
      topConeEdgeChain f hf c hc (bdry2 (orderCx P) (Finsupp.single t 1)) -
        Finsupp.single ((orderCxMap f hf).onF t) 1 := by
  simp [ordTetBoundary, topConeTriangleTetrahedron, topConeEdgeChain, topConeEdgeTriangle,
    bdry2, orderCx, orderCxMap, pathChain]
  rw (config := { transparency := .default }) [map_add, map_add, map_neg]
  rw (config := { transparency := .default }) [Finsupp.linearCombination_single,
    Finsupp.linearCombination_single, Finsupp.linearCombination_single]
  simp only [one_smul]
  abel

theorem topConeTriangleChain_boundary (z : OrdTri P →₀ ℤ) :
    ordBoundary3 (topConeTriangleChain f hf c hc z) =
      topConeEdgeChain f hf c hc (bdry2 (orderCx P) z) - chain2 (orderCxMap f hf) z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => rw (config := { transparency := .default }) [map_add, map_add, hz, hw, map_add, map_add, map_add]; abel
  | single t n =>
      change ordBoundary3 (Finsupp.mapDomain (topConeTriangleTetrahedron f hf c hc)
        (Finsupp.single t n)) = _
      rw (config := { transparency := .default }) [Finsupp.mapDomain_single, ordBoundary3, Finsupp.linearCombination_single,
        topConeTriangleTetrahedron_boundary, smul_sub]
      change _ = _ - Finsupp.mapDomain (orderCxMap f hf).onF (Finsupp.single t n)
      rw (config := { transparency := .default }) [Finsupp.mapDomain_single]
      simp [bdry2]

/-- Negating the upper cone fills an actual mapped two-cycle. -/
theorem topConeTriangleChain_cycle_boundary (z : OrdTri P →₀ ℤ)
    (hz : bdry2 (orderCx P) z = 0) :
    ordBoundary3 (-topConeTriangleChain f hf c hc z) = chain2 (orderCxMap f hf) z := by
  rw (config := { transparency := .default }) [map_neg, topConeTriangleChain_boundary, hz, map_zero, zero_sub, neg_neg]

end FiniteChains.Comb
