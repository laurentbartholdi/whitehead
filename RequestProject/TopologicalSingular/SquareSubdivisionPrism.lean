import RequestProject.TopologicalSingular.SquareSubdivisionGeometry

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

noncomputable def leftSquareSweep (p : GenLoop (Fin 2) X x) :
    ContinuousMap.Homotopy (p.val.comp (leftRectangle 0)) (p.val.comp (leftRectangle squareHalf)) :=
  (ContinuousMap.Homotopy.refl p.val).comp leftRectangleSweep

noncomputable def rightSquareSweep (p : GenLoop (Fin 2) X x) :
    ContinuousMap.Homotopy (p.val.comp (rightRectangle 0)) (p.val.comp (rightRectangle squareHalf)) :=
  (ContinuousMap.Homotopy.refl p.val).comp rightRectangleSweep

theorem squareSweep_common_prism (p : GenLoop (Fin 2) X x) :
    SingularPrism.prism (leftSquareSweep p) 1 (Finsupp.single (cubeEdge 0 1) 1) =
      SingularPrism.prism (rightSquareSweep p) 1 (Finsupp.single (cubeEdge 0 0) 1) := by
  rw [SingularPrism.prism_single, SingularPrism.prism_single, SingularPrism.altSum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply congrArg (fun tau => Finsupp.single tau (1 : ℤ))
  apply ContinuousMap.ext
  intro z
  change p (leftRectangle ((SingularPrism.prismMap i z).1 * squareHalf)
    (cubeEdge 0 1 (SingularPrism.prismMap i z).2)) =
      p (rightRectangle ((SingularPrism.prismMap i z).1 * squareHalf)
        (cubeEdge 0 0 (SingularPrism.prismMap i z).2))
  rw [rectangle_common_edge]

/-- All six outer-edge prisms vanish. The two copies of the moving internal
edge are equal and have opposite signs. -/
theorem squareSweep_boundary_prisms_cancel (p : GenLoop (Fin 2) X x) :
    SingularPrism.prism (leftSquareSweep p) 1 (boundary 1 squareFundamentalChain) +
      SingularPrism.prism (rightSquareSweep p) 1 (boundary 1 squareFundamentalChain) = 0 := by
  have hlh (v : I) (hv : v = 0 ∨ v = 1) :
      SingularPrism.prism (leftSquareSweep p) 1 (Finsupp.single (cubeEdge 1 v) 1) = 0 :=
    SingularPrism.prism_one_single_eq_zero_of_constant _ _ 1 x
      (fun t z => GenLoop.boundary p _ (leftRectangle_horizontal_boundary (t * squareHalf) v hv z))
  have hrh (v : I) (hv : v = 0 ∨ v = 1) :
      SingularPrism.prism (rightSquareSweep p) 1 (Finsupp.single (cubeEdge 1 v) 1) = 0 :=
    SingularPrism.prism_one_single_eq_zero_of_constant _ _ 1 x
      (fun t z => GenLoop.boundary p _ (rightRectangle_horizontal_boundary (t * squareHalf) v hv z))
  have hlo : SingularPrism.prism (leftSquareSweep p) 1 (Finsupp.single (cubeEdge 0 0) 1) = 0 :=
    SingularPrism.prism_one_single_eq_zero_of_constant _ _ 1 x
      (fun t z => GenLoop.boundary p _ (leftRectangle_outer_boundary (t * squareHalf) z))
  have hro : SingularPrism.prism (rightSquareSweep p) 1 (Finsupp.single (cubeEdge 0 1) 1) = 0 :=
    SingularPrism.prism_one_single_eq_zero_of_constant _ _ 1 x
      (fun t z => GenLoop.boundary p _ (rightRectangle_outer_boundary (t * squareHalf) z))
  simp only [squareFundamentalChain_boundary, map_sub, map_add,
    hlh 0 (Or.inl rfl), hlh 1 (Or.inr rfl), hrh 0 (Or.inl rfl), hrh 1 (Or.inr rfl), hlo, hro]
  rw [squareSweep_common_prism]
  abel

theorem squareSweep_left_start (p : GenLoop (Fin 2) X x) :
    map (p.val.comp (leftRectangle 0)) 2 squareFundamentalChain = 0 := by
  have he : p.val.comp (leftRectangle 0) = ContinuousMap.const _ x := by
    apply ContinuousMap.ext
    intro z
    exact GenLoop.boundary p _ (leftRectangle_zero_boundary z)
  rw [he, squareFundamentalChain, map_sub, map_single, map_single]
  exact sub_self _

/-- Splitting the parameter square into two rectangles changes its pushed
fundamental chain by an explicit singular boundary. -/
theorem squareCycle_rectangle_sum_difference_bounds (p : GenLoop (Fin 2) X x) :
    map (p.val.comp (leftRectangle squareHalf)) 2 squareFundamentalChain +
      map (p.val.comp (rightRectangle squareHalf)) 2 squareFundamentalChain - squareCycle p ∈
        LinearMap.range (boundary 2) := by
  refine ⟨SingularPrism.prism (leftSquareSweep p) 2 squareFundamentalChain +
    SingularPrism.prism (rightSquareSweep p) 2 squareFundamentalChain, ?_⟩
  have hl := SingularPrism.prism_identity_succ (leftSquareSweep p) 1 squareFundamentalChain
  have hr := SingularPrism.prism_identity_succ (rightSquareSweep p) 1 squareFundamentalChain
  rw [squareSweep_left_start, sub_zero] at hl
  conv_rhs at hr => rw [rightRectangle_zero, ContinuousMap.comp_id]
  have hz := squareSweep_boundary_prisms_cancel p
  rw [map_add]
  change _ = _ - map p.val 2 squareFundamentalChain
  linear_combination (norm := abel) hl + hr - hz

end FiniteChains.TopologicalSingular
