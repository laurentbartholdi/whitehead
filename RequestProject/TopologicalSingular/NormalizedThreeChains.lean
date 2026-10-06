module

public import RequestProject.TopologicalSingular.CoherentTetrahedronNormalization
public import RequestProject.TopologicalSingular.NormalizedTwoCycles

@[expose] public section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

noncomputable def normalizedTetrahedronChain (x : X) : Chain X 3 →ₗ[ℤ] Chain X 3 :=
  simplexFamilyMap 3 (normalizedTetrahedron x)

theorem normalizedTetrahedronChain_single (x : X) (tau : Simplex X 3) (r : ℤ) :
    normalizedTetrahedronChain x (Finsupp.single tau r) =
      Finsupp.single (normalizedTetrahedron x tau) r :=
  simplexFamilyMap_single 3 (normalizedTetrahedron x) tau r

/-- Normalization commutes exactly with the boundary of every singular
3-chain, not just up to another boundary. -/
theorem normalizedTetrahedronChain_boundary (x : X) (b : Chain X 3) :
    boundary 2 (normalizedTetrahedronChain x b) = normalizedTriangleChain x (boundary 2 b) := by
  induction b using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single tau r =>
    simp only [normalizedTetrahedronChain_single, boundary_single, map_sum, map_zsmul,
      normalizedTriangleChain_single, normalizedTetrahedron_face]

theorem normalizedTetrahedronChain_prism (x : X) (b : Chain X 3) :
    boundary 3 (homotopyFamilyPrism 3 (normalizedTetrahedron x)
      (normalizedTetrahedronHomotopy x) b) +
      homotopyFamilyPrism 2 (normalizedTriangle x) (normalizedTriangleHomotopy x) (boundary 2 b) =
        normalizedTetrahedronChain x b - b :=
  coherentPrism_identity 2 (normalizedTriangle x) (normalizedTetrahedron x)
    (normalizedTriangleHomotopy x) (normalizedTetrahedronHomotopy x)
    (normalizedTetrahedronHomotopy_face x) b

theorem normalizedTetrahedronChain_cycle_difference_bounds (x : X) (b : Chain X 3)
    (hb : boundary 2 b = 0) :
    normalizedTetrahedronChain x b - b ∈ LinearMap.range (boundary 3) :=
  coherentPrism_cycle_difference_bounds 2 (normalizedTriangle x) (normalizedTetrahedron x)
    (normalizedTriangleHomotopy x) (normalizedTetrahedronHomotopy x)
    (normalizedTetrahedronHomotopy_face x) b hb

/-- A filling of a 2-cycle gives an actual filling of its coherent
normalization by tetrahedra whose edges are constant. -/
theorem normalizedTwoCycle_filling (x : X) (c : Chain X 2) (b : Chain X 3)
    (hb : boundary 2 b = c) :
    boundary 2 (normalizedTetrahedronChain x b) = normalizedTriangleChain x c := by
  rw [normalizedTetrahedronChain_boundary, hb]

end FiniteChains.TopologicalSingular
