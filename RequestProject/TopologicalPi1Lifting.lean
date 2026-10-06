module

public import RequestProject.TopologicalCockcroft
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Whitehead
open FiniteChains.TopologicalSingular
variable {X Y E : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]

/-- Triviality on Mathlib's actual fundamental group at every basepoint. -/
def KillsPi1 (f : C(X, Y)) : Prop :=
  ∀ (x : X) (q : FundamentalGroup X x), FundamentalGroup.map f x q = 1

/-- A pi1-trivial map lifts through every covering once a basepoint lift is
specified. This uses the topological lifting criterion, not a combinatorial model. -/
theorem exists_cover_lift_of_killsPi1 [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    (f : C(X, Y)) (hf : KillsPi1 f) (p : C(E, Y)) (hp : IsCoveringMap p)
    (x : X) (e : E) (he : p e = f x) :
    ∃ g : C(X, E), g x = e ∧ p.comp g = f := by
  have hr : (FundamentalGroup.map f x).range ≤
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he).range := by
    intro q hq
    obtain ⟨r, rfl⟩ := hq
    rw [hf x r]
    exact Subgroup.one_mem _
  obtain ⟨g, hg, _⟩ := hp.existsUnique_continuousMap_lifts_of_range_le he hr
  refine ⟨g, hg.1, ?_⟩
  apply ContinuousMap.ext
  intro z
  exact congrFun hg.2 z

/-- The extension-step implication for genuine topology: a pi1-trivial map
out of a Cockcroft space kills pi2 whenever the target has a simply connected cover. -/
theorem killsPi2_of_isCockcroft_of_killsPi1 [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    [SimplyConnectedSpace E] (hX : IsCockcroft X) (f : C(X, Y)) (hf : KillsPi1 f)
    (p : C(E, Y)) (hp : IsCoveringMap p) (hs : Function.Surjective p) : KillsPi2 f := by
  let x : X := Classical.arbitrary X
  obtain ⟨e, he⟩ := hs (f x)
  obtain ⟨g, _, hg⟩ := exists_cover_lift_of_killsPi1 f hf p hp x e he
  rw [← hg]
  exact killsPi2_of_isCockcroft_factorization hX g p

theorem killsPi2_of_acyclic_of_killsPi1 [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    [SimplyConnectedSpace E] (hX : Acyclic X) (f : C(X, Y)) (hf : KillsPi1 f)
    (p : C(E, Y)) (hp : IsCoveringMap p) (hs : Function.Surjective p) : KillsPi2 f :=
  killsPi2_of_isCockcroft_of_killsPi1 (isCockcroft_of_acyclic hX) f hf p hp hs

end Whitehead
