import RequestProject.Framework

/-!
# The hypothesis bundles are consistent

`theoremA` is proved *relative* to the hypotheses collected in
`SufficiencyInputs` and `NecessityInputs`.  A relative theorem is worthless if
its hypotheses are contradictory, since then anything at all would follow.
This file rules that out by exhibiting a model: a `TwoComplexData` for which
both bundles are inhabited.

The model is of course not the geometry of two-complexes; it only witnesses
that the axioms recorded from the paper are mutually consistent, so that
`theoremA` is a genuine implication and not a vacuous one.
-/

namespace FiniteChains

/-- A toy interpretation: "complexes" are natural numbers, "subcomplex" is `≤`, and every
other predicate holds.  Strict inclusions are available because `n < n + 1`. -/
@[reducible] def toyData : TwoComplexData.{0} where
  Cx := ℕ
  Sub := (· ≤ ·)
  sub_refl _ := le_rfl
  sub_trans h h' := le_trans h h'
  Cockcroft _ := True
  ZeroPi2 _ _ := True
  Pi1Trivial _ _ := True
  Acyclic _ := True
  IsAcyclicCover _ _ := True

/-- The replacement data of Section 3 is realized in the toy model. -/
def toyRelativeInputs (D : toyData.Cx) : RelativeInputs toyData D where
  cockcroft_core := trivial
  Y := D + 1
  sub_Y := Nat.le_succ D
  ne_Y := by simp [toyData]
  cockcroft_Y := trivial
  zero_Y := trivial
  pi1_Y := trivial
  repl := id
  term := fun P => P + 1
  repl_core := rfl
  repl_mono _ _ h := h
  repl_strict _ _ _ h := h
  repl_cockcroft _ _ := trivial
  repl_zero _ _ _ _ := trivial
  repl_pi1 _ _ := trivial
  sub_term P _ _ := Nat.le_succ P
  ne_term P _ _ := by simp [toyData]
  cockcroft_term _ _ _ := trivial
  zero_term _ _ _ := trivial
  pi1_term _ _ := trivial

/-- The input for `(2) ⇒ (1)` is realized in the toy model. -/
def toySufficiencyInputs : SufficiencyInputs toyData where
  rel D _ := toyRelativeInputs D
  acyclic_of_cover _ _ _ := trivial
  descent K D c n _ hc := by
    refine ⟨fun i => K + i, rfl, ⟨?_, ?_, ?_⟩, fun _ _ => trivial⟩
    · intro i _; exact Nat.le_succ _
    · intro i _; simp [toyData]
    · intro i _; exact trivial

/-- The input for `(1) ⇒ (2)` is realized in the toy model. -/
def toyNecessityInputs (K : toyData.Cx) : NecessityInputs toyData K where
  G := Unit
  grp := inferInstance
  Req := Unit
  Sat _ _ := True
  chain_subgroups _ _ _ _ := ⟨fun _ => ⊥, fun _ => inferInstance, fun _ _ h => absurd trivial h⟩
  det _ := ⟨∅, fun _ _ _ => Iff.rfl⟩
  sat_sInf_chain _ _ _ _ _ := trivial
  sat_commutator _ _ _ _ := trivial
  cover_of_perfect _ _ _ _ := ⟨0, trivial⟩

/-- Consequently the hypotheses of `theoremA` are consistent. -/
theorem theoremA_inputs_consistent :
    ∃ (W : TwoComplexData.{0}) (_ : SufficiencyInputs W) (K : W.Cx),
      Nonempty (NecessityInputs.{0, 0} W K) :=
  ⟨toyData, toySufficiencyInputs, 0, ⟨toyNecessityInputs 0⟩⟩

end FiniteChains
