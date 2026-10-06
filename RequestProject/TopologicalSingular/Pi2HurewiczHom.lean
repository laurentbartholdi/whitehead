module

public import RequestProject.TopologicalSingular.Pi2HurewiczMap
public import RequestProject.TopologicalSingular.SquareSubdivisionPrism
public import RequestProject.TopologicalSingular.SquareConcatenationGeometry

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular
open CategoryTheory AlgebraicTopology
open scoped Topology
variable {X : Type} [TopologicalSpace X] {x : X}

theorem squareCycle_transAt_difference_bounds (p q : GenLoop (Fin 2) X x) :
    squareCycle p + squareCycle q - squareCycle (GenLoop.transAt 0 p q) ∈
      LinearMap.range (boundary 2) := by
  have he := squareCycle_rectangle_sum_difference_bounds (GenLoop.transAt 0 p q)
  rwa [transAt_leftRectangle, transAt_rightRectangle] at he

theorem squareCycleClass_transAt (p q : GenLoop (Fin 2) X x) :
    singularCycleClass 1 (squareCycle (GenLoop.transAt 0 p q)) (squareCycle_boundary _) =
      singularCycleClass 1 (squareCycle p) (squareCycle_boundary p) +
        singularCycleClass 1 (squareCycle q) (squareCycle_boundary q) := by
  rw [← singularCycleClass_add]
  apply Eq.symm
  exact (singularCycleClass_eq_iff 1 _ _ _ _).mpr (squareCycle_transAt_difference_bounds p q)

theorem pi2CycleClass_mul (x : X) (a b : HomotopyGroup (Fin 2) X x) :
    pi2CycleClass x (a * b) = pi2CycleClass x a + pi2CycleClass x b := by
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      calc
        _ = pi2CycleClass x (Quotient.mk _ (GenLoop.transAt 0 q p)) :=
          congrArg (pi2CycleClass x) (HomotopyGroup.mul_spec (i := (0 : Fin 2)) (p := p) (q := q))
        _ = _ := by
          rw [pi2CycleClass_mk, pi2CycleClass_mk, pi2CycleClass_mk, squareCycleClass_transAt, add_comm]

theorem singularHurewicz2_mul (x : X) (a b : HomotopyGroup (Fin 2) X x) :
    singularHurewicz2 x (a * b) = singularHurewicz2 x a + singularHurewicz2 x b := by
  change (homologyMathlibIso (TopCat.of X) 2).hom (pi2CycleClass x (a * b)) = _
  rw [pi2CycleClass_mul, map_add]
  rfl

/-- The genuine topological Hurewicz homomorphism in degree two. Its group
law is proved using an explicit subdivision of the parameter square. -/
noncomputable def singularHurewicz2Hom (x : X) : HomotopyGroup (Fin 2) X x →*
    Multiplicative
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)) where
  toFun z := Multiplicative.ofAdd (singularHurewicz2 x z)
  map_one' := singularHurewicz2_one x
  map_mul' a b := singularHurewicz2_mul x a b

/-- Vanishing of the genuine Hurewicz image is exactly the existence of an
integral singular filling of the square's fundamental cycle. -/
theorem singularHurewicz2_mk_eq_zero_iff (p : GenLoop (Fin 2) X x) :
    singularHurewicz2 x (Quotient.mk _ p) = 0 ↔
      ∃ b : Chain X 3, boundary 2 b = squareCycle p := by
  have hi := (ModuleCat.mono_iff_injective (homologyMathlibIso (TopCat.of X) 2).hom).mp
    (inferInstance : Mono (homologyMathlibIso (TopCat.of X) 2).hom)
  have he : singularHurewicz2 x (Quotient.mk _ p) = 0 ↔
      singularCycleClass 1 (squareCycle p) (squareCycle_boundary p) = 0 := by
    constructor
    · intro h
      apply hi
      rw [map_zero]
      exact h
    · intro h
      change (homologyMathlibIso (TopCat.of X) 2).hom
        (singularCycleClass 1 (squareCycle p) (squareCycle_boundary p)) = 0
      rw [h, map_zero]
  rw [he]
  constructor
  · intro h
    have hc := (singularCycleClass_eq_iff 1 (squareCycle p) 0 (squareCycle_boundary p) (map_zero _)).mp
      (h.trans (singularCycleClass_zero 1).symm)
    simpa only [sub_zero, LinearMap.mem_range] using hc
  · intro h
    have hc := (singularCycleClass_eq_iff 1 (squareCycle p) 0 (squareCycle_boundary p) (map_zero _)).mpr
      (by simpa only [sub_zero, LinearMap.mem_range] using h)
    exact hc.trans (singularCycleClass_zero 1)

end FiniteChains.TopologicalSingular
