module

public import RequestProject.PresPosetPartialOrder
public import RequestProject.StrictOrderComplex

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α : Type u}

def roseBaseEdge (i : α) (b : Bool) : StrictOrdEdge (Rose α) :=
  ⟨(Rose.base, Rose.edg i b), lt_of_le_of_ne (Rose.base_le_edg i b) (by intro h; cases h)⟩

def roseMidEdge (i : α) (b : Bool) : StrictOrdEdge (Rose α) :=
  ⟨(Rose.mid i, Rose.edg i b), lt_of_le_of_ne (Rose.mid_le_edg i b) (by intro h; cases h)⟩

/-- The actual strict rose edges are exactly the two half-incidences for each generator end. -/
theorem rose_strict_edge_cases (e : StrictOrdEdge (Rose α)) :
    ∃ i b, e = roseBaseEdge i b ∨ e = roseMidEdge i b := by
  rcases e with ⟨⟨a, b⟩, h⟩
  have hl := h.le
  have hn := h.ne
  change Rose.le a b at hl
  cases a with
  | base =>
    cases b with
    | base => exact (hn rfl).elim
    | mid i => exact hl.elim
    | edg i b => exact ⟨i, b, Or.inl (Subtype.ext rfl)⟩
  | mid i =>
    cases b with
    | base => exact hl.elim
    | mid k =>
      change i = k at hl
      subst k
      exact (hn rfl).elim
    | edg k b =>
      change i = k at hl
      subst k
      exact ⟨i, b, Or.inr (Subtype.ext rfl)⟩
  | edg i s =>
    cases b with
    | base => exact hl.elim
    | mid k => exact hl.elim
    | edg k c =>
      change i = k ∧ s = c at hl
      rcases hl with ⟨rfl, rfl⟩
      exact (hn rfl).elim

end FiniteChains.PresModel
