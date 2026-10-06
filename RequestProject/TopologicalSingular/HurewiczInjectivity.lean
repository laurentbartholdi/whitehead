module

public import RequestProject.TopologicalSingular.StationaryPi2Chain
public import RequestProject.TopologicalSingular.StickSimplexQuotient
public import RequestProject.TopologicalSingular.HurewiczSurjectivity

@[expose] public section

namespace FiniteChains.TopologicalSingular
variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- A vanishing genuine Hurewicz class forces the actual based homotopy class
to be trivial. Every square is first represented by a pointed triangle; the
stationary normalization detects its class and kills its singular filling. -/
theorem singularHurewicz2_eq_zero_iff (x : X) (q : HomotopyGroup (Fin 2) X x) :
    singularHurewicz2 x q = 0 ↔ q = 1 := by
  constructor
  · intro hq
    obtain ⟨a, ha⟩ := pointed_triangle_pi2_surjective (Additive.ofMul q)
    have hrep : (Quotient.mk _ (basedTriangleSquare a.map a.based) :
        HomotopyGroup (Fin 2) X x) = q := congrArg Additive.toMul ha
    rw [← hrep] at hq
    obtain ⟨b, hb⟩ := (singularHurewicz2_mk_eq_zero_iff
      (basedTriangleSquare a.map a.based)).mp hq
    have hzero := stationaryPi2Chain_boundary x b
    rw [hb, squareCycle_basedTriangleSquare, stationaryPi2Chain_basedTriangleCycle] at hzero
    exact congrArg Additive.toMul (ha.symm.trans hzero)
  · rintro rfl
    exact singularHurewicz2_one x

theorem singularHurewicz2Hom_injective (x : X) :
    Function.Injective (singularHurewicz2Hom x) := by
  apply (injective_iff_map_eq_one (singularHurewicz2Hom x)).mpr
  intro q hq
  exact (singularHurewicz2_eq_zero_iff x q).mp hq

/-- Injectivity of the degree-two Hurewicz map for simply connected spaces,
with actual Mathlib homotopy groups and integral singular homology. -/
theorem singularHurewicz2_injective (x : X) : Function.Injective (singularHurewicz2 x) := by
  intro a b h
  exact singularHurewicz2Hom_injective x h

theorem pi2CycleClass_injective (x : X) : Function.Injective (pi2CycleClass x) := by
  intro a b h
  apply singularHurewicz2_injective x
  exact congrArg (fun q => (homologyMathlibIso (TopCat.of X) 2).hom q) h

end FiniteChains.TopologicalSingular
