module

public import RequestProject.TopologicalSingular.HurewiczIsomorphism
public import RequestProject.TopologicalSingular.HurewiczSurjectivityConsequences

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular
open CategoryTheory AlgebraicTopology
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- A zero map on integral H2 kills actual pi2 if the target is simply connected. -/
theorem killsPi2_of_singularH2_map_eq_zero [SimplyConnectedSpace Y]
    (f : C(X, Y))
    (hf : (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom f)) = 0) : Whitehead.KillsPi2 f := by
  apply (Whitehead.killsPi2_iff f).mpr
  intro x q
  apply (singularHurewicz2_eq_zero_iff (f x) _).mp
  rw [← singularHurewicz2_natural f x q, hf]
  rfl

theorem killsPi2_iff_singularH2_map_eq_zero [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
    (x : X) (f : C(X, Y)) :
    Whitehead.KillsPi2 f ↔
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom f)) = 0 :=
  ⟨singularH2_map_eq_zero_of_killsPi2 x f, killsPi2_of_singularH2_map_eq_zero f⟩

theorem pi2_subsingleton_of_singularH2_subsingleton [SimplyConnectedSpace X] (x : X)
    [Subsingleton (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of X))] : Subsingleton (HomotopyGroup (Fin 2) X x) :=
  (singularHurewicz2_injective x).subsingleton

/-- In a simply connected space, a square bounds an integral singular 3-chain
if and only if it is null-homotopic relative to its entire boundary. -/
theorem square_bounds_iff_nullhomotopic [SimplyConnectedSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) :
    (∃ b : Chain X 3, boundary 2 b = squareCycle p) ↔
      GenLoop.Homotopic p GenLoop.const := by
  rw [← singularHurewicz2_mk_eq_zero_iff, singularHurewicz2_eq_zero_iff,
    HomotopyGroup.one_def]
  exact ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

end FiniteChains.TopologicalSingular
