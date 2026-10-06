module

public import RequestProject.TopologicalSingular.HurewiczIsomorphismConsequences

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Whitehead
open CategoryTheory AlgebraicTopology FiniteChains.TopologicalSingular
variable {X Y E : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]

/-- The Cockcroft property for actual topological spaces: the canonical
integral degree-two Hurewicz map vanishes at every basepoint. -/
def IsCockcroft (X : Type) [TopologicalSpace X] : Prop :=
  ∀ (x : X) (q : HomotopyGroup (Fin 2) X x), singularHurewicz2 x q = 0

theorem isCockcroft_of_acyclic (hX : Acyclic X) : IsCockcroft X := by
  letI := ModuleCat.isZero_iff_subsingleton.mp (hX 2 (by decide))
  intro x q
  exact Subsingleton.elim _ _

/-- Naturality and injectivity of Hurewicz in the target give the topological
Cockcroft implication, without a simple-connectedness assumption on the source. -/
theorem killsPi2_to_simplyConnected_of_isCockcroft [SimplyConnectedSpace Y]
    (hX : IsCockcroft X) (f : C(X, Y)) : KillsPi2 f := by
  apply (killsPi2_iff f).mpr
  intro x q
  apply (singularHurewicz2_eq_zero_iff (f x) _).mp
  rw [← singularHurewicz2_natural f x q, hX x q, map_zero]

theorem killsPi2_of_isCockcroft_factorization [SimplyConnectedSpace E]
    (hX : IsCockcroft X) (g : C(X, E)) (p : C(E, Y)) : KillsPi2 (p.comp g) := by
  have hg := killsPi2_to_simplyConnected_of_isCockcroft hX g
  intro x a
  have h := mapSquare_homotopic p (hg x a)
  rw [mapSquare_const] at h
  exact h

/-- A zero H2 pushdown along any surjective covering forces the genuine
Cockcroft property downstairs, since every based square lifts. -/
theorem isCockcroft_of_cover_homology_zero (p : C(E, X)) (hp : IsCoveringMap p)
    (hs : Function.Surjective p)
    (hz : (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom p)) = 0) : IsCockcroft X := by
  intro x q
  obtain ⟨e, rfl⟩ := hs x
  obtain ⟨a, rfl⟩ := pi2Map_surjective_of_covering p hp e q
  rw [← singularHurewicz2_natural p e a, hz]
  rfl

theorem cover_homology_zero_of_isCockcroft [SimplyConnectedSpace E]
    (hX : IsCockcroft X) (p : C(E, X)) :
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom p)) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  let e : E := Classical.arbitrary E
  obtain ⟨a, rfl⟩ := singularHurewicz2_surjective e q
  rw [singularHurewicz2_natural]
  exact hX (p e) (pi2Map p e a)

theorem isCockcroft_iff_cover_homology_zero [SimplyConnectedSpace E]
    (p : C(E, X)) (hp : IsCoveringMap p) (hs : Function.Surjective p) :
    IsCockcroft X ↔
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom p)) = 0 :=
  ⟨fun h => cover_homology_zero_of_isCockcroft h p,
    isCockcroft_of_cover_homology_zero p hp hs⟩

/-- The necessary Cockcroft condition for an extension only needs injectivity
of its H2 map; the CW dimension argument is separate from this naturality step. -/
theorem isCockcroft_of_killsPi2_of_homology_injective (f : C(X, Y)) (hf : KillsPi2 f)
    (hi : Function.Injective
      ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom f)).hom)) : IsCockcroft X := by
  intro x q
  apply hi
  rw [map_zero, singularHurewicz2_natural,
    (killsPi2_iff f).mp hf x q, singularHurewicz2_one]

end Whitehead
