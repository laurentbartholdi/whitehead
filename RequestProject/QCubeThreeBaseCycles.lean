import RequestProject.QCubeThreeInternalBoundary
import RequestProject.QCubeCanonicalTwoCycles

/-! Recovered actual square cycles beneath each component of a strict three-boundary. -/
open scoped Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

omit [LinearOrder V] in
theorem qCubeLowerChain_dimension (c : QCube A) (hc : c.spx.card = 3)
    (z : (strictOrderCx (Set.Iio c)).F →₀ ℤ)
    (t : (strictOrderCx (QCube A)).F) (ht : t ∈ (chain2 (strictLowerIncl c) z).support) :
    t.1.2.2.spx.card ≤ 2 := by
  classical
  change t ∈ (Finsupp.mapDomain (strictLowerIncl c).onF z).support at ht
  obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ht)
  change s.1.2.2.1.spx.card ≤ 2
  have hd := qCube_card_lt_of_lt s.1.2.2.2
  rw (config := { transparency := .default }) [hc] at hd
  omega

/-- Every isolated three-cube component has an actual lower two-cycle whose projected
chain is exactly a finite square-chain subdivision. -/
theorem qCube_three_component_square_cycle (c : QCube A) (hc : c.spx.card = 3)
    (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2) :
    ∃ (z : (strictOrderCx (Set.Iio c)).F →₀ ℤ) (r : QSquare A →₀ ℤ),
      Comb.bdry2 (strictOrderCx (Set.Iio c)) z = 0 ∧
      qSquareFacetBoundary r = 0 ∧
      qSquareChainSubdivision r = chain2 (strictLowerIncl c) z ∧
      strictTopConeTriangleChain Subtype.val (fun _ _ h => h) c
        (fun x : Set.Iio c => x.2) z = y.filter (fun t => t.1.2.2.2 = c) := by
  obtain ⟨z, hz, hfan⟩ := qCube_three_component_lower_cycle c hc y hy hb
  have hcycle : Comb.bdry2 (strictOrderCx (QCube A)) (chain2 (strictLowerIncl c) z) = 0 := by
    rw (config := { transparency := .default }) [bdry2_chain2, hz, map_zero]
  refine ⟨z, qSquareCycleCoefficients (chain2 (strictLowerIncl c) z), hz,
    qCube_twoCycle_coefficients_cycle _ (qCubeLowerChain_dimension c hc z) hcycle,
    qCube_twoCycle_reconstruction _ (qCubeLowerChain_dimension c hc z) hcycle, hfan⟩

/-- Recovered square coefficients of a lower-interval chain are supported on actual facets. -/
theorem qSquare_lower_coefficients_support (c : QCube A) (hc : c.spx.card = 3)
    (z : (strictOrderCx (Set.Iio c)).F →₀ ℤ) (s : QSquare A)
    (hs : s ∈ (qSquareCycleCoefficients (chain2 (strictLowerIncl c) z)).support) :
    ∃ v ∈ c.spx, s.1 = qCubeFacet c v 0 ∨ s.1 = qCubeFacet c v 1 := by
  classical
  have hn := Finsupp.mem_support_iff.mp hs
  change (chain2 (strictLowerIncl c) z)
    (squareFlag s.1 (qSquareLeft s) (qSquareRight s) (qSquare_directions_ne s)
      (qSquare_free_directions s) (false, 0, false)) ≠ 0 at hn
  have hmem := Finsupp.mem_support_iff.mpr hn
  change _ ∈ (Finsupp.mapDomain (strictLowerIncl c).onF z).support at hmem
  obtain ⟨t, _, he⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hmem)
  have htop : t.1.2.2.1 = s.1 := by
    have h := congrArg (fun t : (strictOrderCx (QCube A)).F => t.1.2.2) he
    simpa only [strictLowerIncl, strictOrderCxMap, squareFlag_top] using h
  have hlt := t.1.2.2.2
  rw (config := { transparency := .default }) [htop] at hlt
  exact exists_qCube_zero_or_one_facet s.1 c hlt.le (by rw (config := { transparency := .default }) [hc, s.2])

/-- The isolated three-cube boundary is the negative subdivision of an actual finite
square cycle supported on that cube's six coordinate facets. -/
theorem qCube_three_component_facet_boundary (c : QCube A) (hc : c.spx.card = 3)
    (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2) :
    ∃ r : QSquare A →₀ ℤ,
      qSquareFacetBoundary r = 0 ∧
      (∀ s ∈ r.support, ∃ v ∈ c.spx, s.1 = qCubeFacet c v 0 ∨ s.1 = qCubeFacet c v 1) ∧
      qSquareChainSubdivision r = -strictOrdBoundary3 (y.filter (fun t => t.1.2.2.2 = c)) := by
  obtain ⟨z, hz, hfan⟩ := qCube_three_component_lower_cycle c hc y hy hb
  have hcycle : Comb.bdry2 (strictOrderCx (QCube A)) (chain2 (strictLowerIncl c) z) = 0 := by
    rw (config := { transparency := .default }) [bdry2_chain2, hz, map_zero]
  refine ⟨qSquareCycleCoefficients (chain2 (strictLowerIncl c) z),
    qCube_twoCycle_coefficients_cycle _ (qCubeLowerChain_dimension c hc z) hcycle,
    qSquare_lower_coefficients_support c hc z, ?_⟩
  rw (config := { transparency := .default }) [qCube_twoCycle_reconstruction _ (qCubeLowerChain_dimension c hc z) hcycle,
    ← hfan, strictTopConeTriangleChain_boundary, hz, map_zero, zero_sub, neg_neg]
  rfl

end FiniteChains.Davis
