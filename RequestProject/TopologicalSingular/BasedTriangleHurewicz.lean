import RequestProject.TopologicalSingular.TriangleSquareGeometry
import RequestProject.TopologicalSingular.Pi2HurewiczHom

namespace FiniteChains.TopologicalSingular
open CategoryTheory AlgebraicTopology
open scoped Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

theorem basedTriangle_eq_of_zero_coordinate (tau : Simplex X 2)
    (h : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x)
    (z : Domain 2) (i : Fin 3) (hi : z.val i = 0) : tau z = x := by
  obtain ⟨w, hw⟩ := domain_zero_coordinate_face z i hi
  have he := congrArg (fun f : Simplex X 1 => f w) (h i)
  change tau (stdSimplex.map (SimplexCategory.δ i) w) = x at he
  rwa [hw] at he

/-- A triangle with all three faces at the basepoint is an actual based
square, by collapsing the upper triangle of the square onto an edge. -/
noncomputable def basedTriangleSquare (tau : Simplex X 2)
    (h : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x) : GenLoop (Fin 2) X x :=
  ⟨tau.comp squareToTriangle, by
    intro z hz
    obtain ⟨i, hi⟩ := squareToTriangle_boundary z hz
    exact basedTriangle_eq_of_zero_coordinate tau h _ i hi⟩

noncomputable def basedTriangleCycle (tau : Simplex X 2) (x : X) : Chain X 2 :=
  Finsupp.single tau 1 - Finsupp.single (ContinuousMap.const (Domain 2) x) 1

theorem basedTriangleCycle_boundary (tau : Simplex X 2)
    (h : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x) :
    boundary 1 (basedTriangleCycle tau x) = 0 := by
  rw [basedTriangleCycle, map_sub, boundary_two_single, boundary_constant_two, h 0, h 1, h 2]
  abel

/-- Exact chain identity; no subdivision or comparison hypothesis is used. -/
theorem squareCycle_basedTriangleSquare (tau : Simplex X 2)
    (h : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x) :
    squareCycle (basedTriangleSquare tau h) = basedTriangleCycle tau x := by
  have he1 : simplexMap (basedTriangleSquare tau h).val 2 cubeTriangle1 = tau := by
    apply ContinuousMap.ext
    intro z
    change tau (squareToTriangle (cubeTriangle1 z)) = tau z
    rw [squareToTriangle_triangle1]
  have he0 : simplexMap (basedTriangleSquare tau h).val 2 cubeTriangle0 =
      ContinuousMap.const (Domain 2) x := by
    apply ContinuousMap.ext
    intro z
    exact basedTriangle_eq_of_zero_coordinate tau h _ 1 (squareToTriangle_triangle0_zero z)
  rw [squareCycle, squareFundamentalChain, map_sub, map_single, map_single, he1, he0]
  rfl

end FiniteChains.TopologicalSingular

namespace FiniteChains.TopologicalSingular
open CategoryTheory AlgebraicTopology
open scoped Topology
variable {X : Type} [TopologicalSpace X] {x : X}

/-- Every normalized based singular triangle is in the image of the genuine
topological Hurewicz homomorphism. -/
theorem basedTriangle_hurewicz_representative (tau : Simplex X 2)
    (h : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x) :
    singularHurewicz2 x (Quotient.mk _ (basedTriangleSquare tau h)) =
      (homologyMathlibIso (TopCat.of X) 2).hom
        (singularCycleClass 1 (basedTriangleCycle tau x) (basedTriangleCycle_boundary tau h)) := by
  simp only [singularHurewicz2, pi2CycleClass_mk, squareCycle_basedTriangleSquare]

end FiniteChains.TopologicalSingular
