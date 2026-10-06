module

public import RequestProject.RollerGraphMetric

@[expose] public section

/-!
# Non-vacuity of the gated Roller model

The hypotheses collected in `FiniteChains.GatedRollerModel` are satisfiable: the three-cube,
whose vertices are all subsets of a three-element set of hyperplanes, is a gated Roller model,
and the complex it defines has a genuine three-dimensional cell.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open RollerBridge

set_option maxRecDepth 100000

/-- The three-cube as a gated Roller model: the vertices are all subsets of a three-element
set of hyperplanes. -/
noncomputable def cubeGatedModel : GatedRollerModel (Fin 3) where
  W := Set.univ
  base_mem := trivial
  med_mem := fun _ _ _ => trivial
  dim_le := by
    intro A _ s hs
    have h : ∀ B ∈ s, B ⊆ A ∧ B.card + 1 = A.card := fun B hB => ⟨(hs B hB).2.1, (hs B hB).2.2⟩
    revert h
    revert A s
    decide
  step := by
    intro A B _ _ hne
    have h : ∃ C : Finset (Fin 3), dsym A C = 1 ∧ dsym C B + 1 = dsym A B := by
      revert hne
      revert A B
      decide
    obtain ⟨C, h1, h2⟩ := h
    exact ⟨C, trivial, h1, h2⟩

/-- In the three-cube the graph distance is the number of separating hyperplanes; for instance
the two opposite vertices `∅` and `{0, 1, 2}` are at distance three. -/
theorem cubeGatedModel_dist :
    (cubeGatedModel.graph).dist ⟨∅, trivial⟩ ⟨{0, 1, 2}, trivial⟩ = 3 := by
  rw [cubeGatedModel.dist_eq_dsym]
  decide

/-- The complex of the three-cube has a three-dimensional cell. -/
theorem cubeGatedModel_nonempty_CbC :
    Nonempty ((cubeGatedModel.toMedianSimpleGraph).toDescCubeStr).CbC := by
  set w : cubeGatedModel.Vtx := ⟨{0, 1, 2}, trivial⟩ with hw
  set a : cubeGatedModel.Vtx := ⟨{1, 2}, trivial⟩ with ha
  set b : cubeGatedModel.Vtx := ⟨{0, 2}, trivial⟩ with hb
  set c : cubeGatedModel.Vtx := ⟨{0, 1}, trivial⟩ with hc
  have hmem : ∀ x : cubeGatedModel.Vtx, dsym x.1 w.1 = 1 → dsym (∅ : Finset (Fin 3)) x.1 + 1 =
      dsym (∅ : Finset (Fin 3)) w.1 →
      x ∈ ((cubeGatedModel.toMedianSimpleGraph).toDescCubeStr).dn w := by
    intro x h1 h2
    refine ⟨?_, ?_⟩
    · show (cubeGatedModel.graph).dist x w = 1
      rw [cubeGatedModel.dist_eq_dsym]
      exact h1
    · show (cubeGatedModel.graph).dist ⟨∅, trivial⟩ x + 1 =
        (cubeGatedModel.graph).dist ⟨∅, trivial⟩ w
      rw [cubeGatedModel.dist_eq_dsym, cubeGatedModel.dist_eq_dsym]
      exact h2
  refine DescCubeStr.nonempty_CbC (w := w) (a := a) (b := b) (c := c)
    (hmem a (by decide) (by decide)) (hmem b (by decide) (by decide))
    (hmem c (by decide) (by decide)) ?_ ?_ ?_ <;>
    · intro h
      have := congrArg Subtype.val h
      revert this
      decide

end FiniteChains
