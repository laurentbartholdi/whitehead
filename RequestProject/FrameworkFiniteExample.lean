module

public import RequestProject.FrameworkFinite
public import RequestProject.Consistency

@[expose] public section

/-!
# The finiteness input is consistent

As in `RequestProject/Consistency.lean`, a relative statement is worthless if its hypotheses
are contradictory.  Here the finiteness input of `RequestProject/FrameworkFinite.lean` is
realised in the same toy model: `FiniteChains.toyFinitenessInputs`, whence
`FiniteChains.finitenessInputs_consistent`.
-/

namespace FiniteChains

/-- The finiteness input is realised in the toy model of `Consistency.lean`. -/
def toyFinitenessInputs (D : toyData.Cx) : FinitenessInputs (toyRelativeInputs D) where
  Fin _ := True
  fin_core := trivial
  fin_Y := trivial
  fin_repl _ _ := trivial
  fin_term _ _ := trivial

/-- Consequently the finiteness supplement is not vacuous: its hypotheses are consistent. -/
theorem finitenessInputs_consistent :
    ∃ (W : TwoComplexData.{0}) (D : W.Cx) (h : RelativeInputs W D), Nonempty (FinitenessInputs h) :=
  ⟨toyData, 0, toyRelativeInputs 0, ⟨toyFinitenessInputs 0⟩⟩

end FiniteChains
