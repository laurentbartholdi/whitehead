module

public import RequestProject.CanonicalPresentationTopologicalChains
public import RequestProject.PresentationChainFinsupp

@[expose] public section

namespace FiniteChains
open PresModel
variable {α J : Type} {ρ : J → FreeGroup α} {n : ℕ}

namespace PresChainFS
variable (h : PresChainFS ρ n)

/-- The actual CW realization of a specified stage of an existing algebraic
presentation chain. It is connected and genuinely two-dimensional. -/
noncomputable def stageTwoComplex (i : ℕ) (a : h.gen i) : Whitehead.TwoComplex :=
  letI := h.decGen i
  validPresTwoComplex (presCanonicalWords (h.rel i) a)
    (presCanonicalWords_ne_nil (h.rel i) a)

/-- Realize an existing algebraic chain as the exact topological HasChain
starting at its zeroth stage. The original structure merely embeds the
external presentation rho into that stage; no equality with rho is assumed. -/
theorem hasTopologicalChain (a : h.gen 0)
    (hp : ∀ i, i < n → (∃ b : h.gen (i + 1), b ∉ Set.range (h.genIncl i)) ∨
      ∃ j : h.cell (i + 1), j ∉ Set.range (h.cellIncl i))
    (finite : Bool) (hfin : finite = true → Finite (h.gen n) ∧ Finite (h.cell n)) :
    Whitehead.HasChain (h.stageTwoComplex 0 a) n finite := by
  letI : ∀ i, DecidableEq (h.gen i) := h.decGen
  exact canonical_hasChain_of_presentations h.rel
    (fun i => ⟨h.genIncl i, h.genIncl_injective i⟩)
    (fun i => ⟨h.cellIncl i, h.cellIncl_injective i⟩)
    h.rel_incl a n hp h.zero_pi2 finite hfin

end PresChainFS

namespace PresChain
variable (h : PresChain ρ n)

/-- Forget only the finiteness witnesses, retaining the same presentation
chain, inclusions, and algebraic universal-cover cycle calculation. -/
def toPresChainFS : PresChainFS ρ n where
  gen := h.gen
  cell := h.cell
  decGen := h.decGen
  rel := h.rel
  genIncl := h.genIncl
  genIncl_injective := h.genIncl_injective
  cellIncl := h.cellIncl
  cellIncl_injective := h.cellIncl_injective
  rel_incl := h.rel_incl
  baseGen := h.baseGen
  baseGen_injective := h.baseGen_injective
  baseCell := h.baseCell
  baseCell_injective := h.baseCell_injective
  rel_base := h.rel_base
  zero_pi2 := h.zero_pi2

/-- Existing finite algebraic presentation chains now produce actual finite
CW chains of the same length, with the initial stage's open cells preserved. -/
theorem hasFiniteTopologicalChain (a : h.gen 0)
    (hp : ∀ i, i < n → (∃ b : h.gen (i + 1), b ∉ Set.range (h.genIncl i)) ∨
      ∃ j : h.cell (i + 1), j ∉ Set.range (h.cellIncl i)) :
    Whitehead.HasChain (h.toPresChainFS.stageTwoComplex 0 a) n true := by
  apply h.toPresChainFS.hasTopologicalChain a hp true
  intro _
  change Finite (h.gen n) ∧ Finite (h.cell n)
  letI := h.finGen n
  letI := h.finCell n
  exact ⟨inferInstance, inferInstance⟩

end PresChain
end FiniteChains
