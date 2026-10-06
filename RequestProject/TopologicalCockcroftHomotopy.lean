module

public import RequestProject.TopologicalCockcroft
public import RequestProject.TopologicalSingular.MathlibComparison

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Whitehead
open CategoryTheory AlgebraicTopology FiniteChains.TopologicalSingular
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- A left homotopy inverse makes the actual integral singular-homology map injective. -/
theorem singularHomologyMap_injective_of_leftHomotopyInverse
    (f : C(X, Y)) (g : C(Y, X)) (h : (g.comp f).Homotopic (ContinuousMap.id X)) (n : ℕ) :
    Function.Injective
      ((((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom f)).hom) := by
  let F := (singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)
  have hr : F.map (TopCat.ofHom f) ≫ F.map (TopCat.ofHom g) = 𝟙 (F.obj (TopCat.of X)) := by
    rw [← Functor.map_comp]
    exact (mathlibHomologyMap_eq_of_homotopic
      (TopCat.ofHom (g.comp f)) (𝟙 (TopCat.of X)) h n).trans (F.map_id _)
  intro a b hab
  have hm := congrArg (fun z => (F.map (TopCat.ofHom g)).hom z) hab
  have ha := congrArg (fun k => k.hom a) hr
  have hb := congrArg (fun k => k.hom b) hr
  change (F.map (TopCat.ofHom g)).hom ((F.map (TopCat.ofHom f)).hom a) = a at ha
  change (F.map (TopCat.ofHom g)).hom ((F.map (TopCat.ofHom f)).hom b) = b at hb
  exact ha.symm.trans (hm.trans hb)

theorem isCockcroft_of_homology_injective (f : C(X, Y))
    (hi : Function.Injective
      ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom f)).hom)) (hY : IsCockcroft Y) : IsCockcroft X := by
  intro x q
  apply hi
  rw [map_zero, singularHurewicz2_natural, hY]

/-- The genuine Hurewicz-zero property is invariant under an actual homotopy equivalence. -/
theorem isCockcroft_iff_of_homotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y) :
    IsCockcroft X ↔ IsCockcroft Y :=
  ⟨fun hX => isCockcroft_of_homology_injective e.invFun
      (singularHomologyMap_injective_of_leftHomotopyInverse e.invFun e.toFun e.right_inv 2) hX,
    fun hY => isCockcroft_of_homology_injective e.toFun
      (singularHomologyMap_injective_of_leftHomotopyInverse e.toFun e.invFun e.left_inv 2) hY⟩

end Whitehead
