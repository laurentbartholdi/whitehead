module

public import RequestProject.SquareComplexTreeCase

@[expose] public section

/-!
# The one-dimensional criterion is not vacuous

The simplest square complex without two-cells — two vertices joined by one edge — is connected
and simply connected, so `FiniteChains.SquareComplex.medianSimpleGraph_of_simplyConnected`
applies to it and produces a median graph.
-/

namespace FiniteChains

/-- Two vertices joined by an edge, with no two-cells. -/
def edgeComplex : SquareComplex Bool where
  adj a b := a ≠ b
  adj_symm h := Ne.symm h
  adj_irrefl _ h := h rfl
  sq _ _ _ _ := False
  sq_adj h := h.elim
  sq_rotate h := h
  sq_reverse h := h

theorem edgeComplex_no_square (a b c d : Bool) : ¬ edgeComplex.sq a b c d := id

theorem bool_eq_of_ne_ne {a b c : Bool} (hab : a ≠ b) (hbc : b ≠ c) : c = a := by
  revert hab hbc
  rcases a <;> rcases b <;> rcases c <;> simp

/-- In the one-edge complex every closed walk contracts: after the first step the walk must come
straight back, which is a backtrack. -/
theorem edgeComplex_simplyConnected : edgeComplex.SimplyConnected := by
  intro x l hl
  -- induction on the length of the walk
  obtain ⟨n, hn⟩ : ∃ n, l.length ≤ n := ⟨l.length, le_rfl⟩
  induction n generalizing l x with
  | zero =>
      obtain ⟨-, hh, -⟩ := hl
      rcases l with _ | ⟨a, t⟩
      · simp at hh
      · simp at hn
  | succ n ih =>
      obtain ⟨hw, hh, hlast⟩ := hl
      rcases l with _ | ⟨a, t⟩
      · simp at hh
      have hax : a = x := by simpa using hh
      subst hax
      rcases t with _ | ⟨b, t⟩
      · exact SquareComplex.Homotopic.refl _
      have hab : a ≠ b := (List.isChain_cons_cons.1 hw).1
      rcases t with _ | ⟨c, t⟩
      · -- a walk `a, b` cannot be closed
        exfalso
        have : b = a := by simpa using hlast
        exact hab this.symm
      have hbc : b ≠ c := (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hw).2).1
      have hca : c = a := bool_eq_of_ne_ne hab hbc
      rw [hca] at hw hlast ⊢
      -- cancel the backtrack `a, b, a`
      have hmove : edgeComplex.Move (a :: b :: a :: t) (a :: t) :=
        SquareComplex.Move.backtrack a b t
      refine SquareComplex.Homotopic.head_move hmove (ih (x := a) (l := a :: t) ⟨?_, rfl, ?_⟩ ?_)
      · exact hmove.isWalk hw
      · simpa using hlast
      · simp at hn ⊢
        omega

theorem edgeComplex_connected : (SquareComplex.toSimpleGraph edgeComplex).Connected := by
  have hpre : (SquareComplex.toSimpleGraph edgeComplex).Preconnected := by
    intro u v
    by_cases h : u = v
    · subst h
      exact SimpleGraph.Reachable.refl u
    · exact SimpleGraph.Adj.reachable (show edgeComplex.adj u v from h)
  exact SimpleGraph.Connected.mk hpre

open Classical in
/-- **Non-vacuity of the one-dimensional criterion**: the one-edge complex is connected, simply
connected and has no two-cells, so its one-skeleton is a median graph. -/
noncomputable def edgeComplexMedian : MedianSimpleGraph Bool :=
  SquareComplex.medianSimpleGraph_of_simplyConnected edgeComplex_no_square
    edgeComplex_simplyConnected edgeComplex_connected true

theorem edgeComplexMedian_adj (a b : Bool) : edgeComplexMedian.G.Adj a b ↔ a ≠ b := Iff.rfl

end FiniteChains
