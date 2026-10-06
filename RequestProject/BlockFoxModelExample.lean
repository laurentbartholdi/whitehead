module

public import RequestProject.BlockFoxModel
public import RequestProject.GenerationIterate

@[expose] public section

/-!
# The hypotheses of the constructed block model are satisfiable

`RequestProject/BlockFoxModel.lean` proves property (B2) — equation (3.3) — for a structural
map which carries the chain model of the double mapping cylinder, the dictionary between that
model and the Fox complex being part of the construction rather than a hypothesis.  This file
checks that the remaining hypotheses (the exactness of the pair and the vanishing of the
relative second homology) are consistent, by instantiating them in the degenerate case of the
identity substitution: the replaced two-cell and the relative complex are zero, the preimage
of `X` is the whole complex, and the conclusion is the (true) generation statement for the
identity structural map.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace BlockFoxExample

open MonoidAlgebra

universe u

variable {α J : Type u} [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
  (ρ : J → FreeGroup α)

omit [DecidableEq J] in
/-- The coefficient map of the identity structural map is the identity. -/
theorem pushRing_id (x : MonoidAlgebra ℤ (PresGroup ρ)) :
    (PresMor.id ρ).pushRing x = x :=
  MonoidAlgebra.mapDomain_id x

/-- The base change of the chain map of the identity structural map is the identity. -/
theorem cellsBase_id (y : J → MonoidAlgebra ℤ (PresGroup ρ)) :
    (PresMor.id ρ).cellsBase y = y :=
  (PresMor.chain_eq_sum_single y).symm

/-- The degenerate chain model: no replaced two-cell, no relative complex. -/
abbrev Triv : Type u := Fin 0 → MonoidAlgebra ℤ (PresGroup ρ)

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] in
theorem triv_eq_zero (x : Triv ρ) : x = 0 := by
  funext i
  exact i.elim0

/-- **The hypotheses of `FiniteChains.BlockFox.generates_of_fox_chain_model` are
satisfiable.**  For the identity substitution they hold with the zero chain model, and the
conclusion is equation (3.3) for the identity structural map. -/
theorem generates_id : Generates (PresMor.id ρ) := by
  classical
  refine BlockFox.generates_of_fox_chain_model (Q := Triv ρ) (B₃ := Triv ρ) (Q₃ := Triv ρ)
    (Q₂ := Triv ρ) (Q₁ := Triv ρ) (PresMor.id ρ) (fun _ _ h => h) 0 0
    (LinearEquiv.refl _ _) 0 0 LinearMap.id LinearMap.id 0 0 (fun _ _ h => h) ?_
    (fun y => ⟨y, rfl⟩) ?_ (fun _ => rfl) (fun _ => rfl) ?_ ?_
  · -- exactness: the preimage of `X` is everything
    intro z _
    refine ⟨z.1, ?_⟩
    rw [BlockFox.inclModel_apply, cellsBase_id]
    exact Prod.ext rfl (triv_eq_zero ρ z.2).symm
  · -- the inclusion is a chain map
    intro a
    rw [BlockFox.inclModel_apply, cellsBase_id]
    show BlockFox.bdry₂model (Q := Triv ρ) 0 (a, 0) = _
    rw [BlockFox.bdry₂model_inl]
    funext i
    show ∑ j, a j * foxMatrixPres ρ i j = ∑ j, a j * (PresMor.id ρ).pushRing (foxMatrixPres ρ i j)
    exact Finset.sum_congr rfl fun j _ => by rw [pushRing_id]
  · -- the boundary of the cancelled three-cells vanishes
    intro y
    simp [BlockFox.bdry₂model]
  · -- the relative second homology vanishes
    intro q _
    exact ⟨0, (triv_eq_zero ρ q).symm⟩

end BlockFoxExample
end FiniteChains
