module

public import RequestProject.SquareComplexWalls

@[expose] public section

/-!
# The four-cycle with its square: non-vacuity of the wall theorems

`RequestProject/SquareComplexWalls.lean` proves that in a simply connected square complex every
square-closed family of edges is two-sided.  Here the hypotheses are checked on an explicit
complex which really has a two-cell: the four-cycle `ZMod 4` with its square glued in
(`FiniteChains.cycleFour`).  We prove

* `FiniteChains.cycleFour_simplyConnected` — every closed walk contracts by elementary moves, so
  the complex is simply connected (this is where the two-cell is used);
* `FiniteChains.cycleFour_connected` — it is connected;
* `FiniteChains.cycleFour_bipartition`, `FiniteChains.cycleFour_wall` — the conclusions of
  `SquareComplex.exists_bipartition` and `SquareComplex.exists_side` therefore apply to it;
* `FiniteChains.cycleFourNoSquare_not_simplyConnected` — the same graph *without* the two-cell is
  not simply connected, so the two-cell is genuinely needed and the notion of simple connectivity
  used in the wall theorems is not vacuous.
-/

namespace FiniteChains

/-- Adjacency of the four-cycle. -/
def cycleFourAdj (x y : ZMod 4) : Prop := y = x + 1 ∨ y = x - 1

instance : DecidableRel cycleFourAdj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The single two-cell of the four-cycle, read from any vertex and in either orientation. -/
def cycleFourSq (a b c d : ZMod 4) : Prop :=
  (b = a + 1 ∧ c = a + 2 ∧ d = a + 3) ∨ (b = a - 1 ∧ c = a - 2 ∧ d = a - 3)

instance : ∀ a b c d, Decidable (cycleFourSq a b c d) := fun _ _ _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

theorem cycleFourAdj_symm : ∀ a b : ZMod 4, cycleFourAdj a b → cycleFourAdj b a := by decide

theorem cycleFourAdj_irrefl : ∀ a : ZMod 4, ¬ cycleFourAdj a a := by decide

theorem cycleFourSq_adj : ∀ a b c d : ZMod 4, cycleFourSq a b c d →
    cycleFourAdj a b ∧ cycleFourAdj b c ∧ cycleFourAdj c d ∧ cycleFourAdj d a := by decide

theorem cycleFourSq_rotate : ∀ a b c d : ZMod 4, cycleFourSq a b c d → cycleFourSq b c d a := by
  decide

theorem cycleFourSq_reverse : ∀ a b c d : ZMod 4, cycleFourSq a b c d → cycleFourSq d c b a := by
  decide

/-- The four-cycle with its square glued in. -/
def cycleFour : SquareComplex (ZMod 4) where
  adj := cycleFourAdj
  adj_symm := fun {a b} h => cycleFourAdj_symm a b h
  adj_irrefl := cycleFourAdj_irrefl
  sq := cycleFourSq
  sq_adj := fun {a b c d} h => cycleFourSq_adj a b c d h
  sq_rotate := fun {a b c d} h => cycleFourSq_rotate a b c d h
  sq_reverse := fun {a b c d} h => cycleFourSq_reverse a b c d h

/-- The complex really has a two-cell. -/
theorem cycleFour_has_square : cycleFour.sq 0 1 2 3 := (by decide : cycleFourSq 0 1 2 3)

/-- A chain for the adjacency relation is a walk of the complex. -/
theorem cycleFour_isWalk {l : List (ZMod 4)} (h : List.IsChain cycleFourAdj l) :
    cycleFour.IsWalk l := h

/-- Three consecutive edges of the four-cycle that do not backtrack span the square. -/
theorem cycleFour_three_span : ∀ a b c u : ZMod 4, cycleFourAdj a b → cycleFourAdj b c →
    cycleFourAdj c u → c ≠ a → u ≠ b → cycleFourSq a b c u := by decide

/-- Every closed walk of the four-cycle contracts to its base point: the complex is simply
connected. -/
theorem cycleFour_simplyConnected : cycleFour.SimplyConnected := by
  have key : ∀ (n : ℕ) (x : ZMod 4) (l : List (ZMod 4)), l.length ≤ n →
      cycleFour.IsClosedWalk x l → cycleFour.Homotopic l [x] := by
    intro n
    induction n with
    | zero =>
        intro x l hlen hcw
        have : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
        rw [this] at hcw
        exact absurd hcw.2.1 (by simp)
    | succ n ih =>
        intro x l hlen hcw
        match l with
        | [] => exact absurd hcw.2.1 (by simp)
        | [a] =>
            have hax : a = x := by simpa using hcw.2.1
            rw [hax]
            exact SquareComplex.Homotopic.refl _
        | [a, b] =>
            exfalso
            have hax : a = x := by simpa using hcw.2.1
            have hbx : b = x := by simpa using hcw.2.2
            have hab : cycleFour.adj a b := (List.isChain_cons_cons.mp hcw.1).1
            rw [hax, hbx] at hab
            exact cycleFour.adj_irrefl x hab
        | a :: b :: c :: t =>
            have hchain := hcw.1
            have hab : cycleFour.adj a b := (List.isChain_cons_cons.mp hchain).1
            have hbc : cycleFour.adj b c :=
              (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hchain).2).1
            by_cases hca : c = a
            · subst hca
              have hmove : cycleFour.Move (c :: b :: c :: t) (c :: t) :=
                SquareComplex.Move.backtrack c b t
              refine SquareComplex.Homotopic.head_move hmove (ih x (c :: t) ?_ ?_)
              · simp only [List.length_cons] at hlen ⊢; omega
              · exact SquareComplex.IsClosedWalk.of_move hmove hcw
            · match t with
              | [] =>
                  exfalso
                  have hax : a = x := by simpa using hcw.2.1
                  have hcx : c = x := by simpa using hcw.2.2
                  exact hca (by rw [hax, hcx])
              | u :: t' =>
                  have hcu : cycleFour.adj c u :=
                    (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp
                      (List.isChain_cons_cons.mp hchain).2).2).1
                  by_cases hub : u = b
                  · subst hub
                    have hmove : cycleFour.Move (a :: u :: c :: u :: t') (a :: u :: t') :=
                      SquareComplex.Move.cons a (SquareComplex.Move.backtrack u c t')
                    refine SquareComplex.Homotopic.head_move hmove (ih x (a :: u :: t') ?_ ?_)
                    · simp only [List.length_cons] at hlen ⊢; omega
                    · exact SquareComplex.IsClosedWalk.of_move hmove hcw
                  · have hsq : cycleFour.sq a b c u :=
                      cycleFour_three_span a b c u hab hbc hcu hca hub
                    have hmove1 : cycleFour.Move (a :: b :: c :: u :: t') (a :: u :: c :: u :: t') :=
                      SquareComplex.Move.square hsq (u :: t')
                    have hmove2 : cycleFour.Move (a :: u :: c :: u :: t') (a :: u :: t') :=
                      SquareComplex.Move.cons a (SquareComplex.Move.backtrack u c t')
                    refine SquareComplex.Homotopic.head_move hmove1
                      (SquareComplex.Homotopic.head_move hmove2 (ih x (a :: u :: t') ?_ ?_))
                    · simp only [List.length_cons] at hlen ⊢; omega
                    · exact SquareComplex.IsClosedWalk.of_move hmove2
                        (SquareComplex.IsClosedWalk.of_move hmove1 hcw)
  intro x l hl
  exact key l.length x l le_rfl hl

/-- The four-cycle is connected. -/
theorem cycleFour_connected : ∀ v : ZMod 4, ∃ l, cycleFour.IsWalkFrom 0 v l := by
  intro v
  fin_cases v
  · exact ⟨[0], List.isChain_singleton .., rfl, rfl⟩
  · exact ⟨[0, 1], cycleFour_isWalk (by decide), rfl, rfl⟩
  · exact ⟨[0, 1, 2], cycleFour_isWalk (by decide), rfl, rfl⟩
  · exact ⟨[0, 1, 2, 3], cycleFour_isWalk (by decide), rfl, rfl⟩

/-- The one-skeleton of the four-cycle is bipartite, by the general theorem. -/
theorem cycleFour_bipartition :
    ∃ σ : ZMod 4 → ZMod 2, ∀ u v : ZMod 4, cycleFour.adj u v → σ u ≠ σ v :=
  SquareComplex.exists_bipartition cycleFour_simplyConnected cycleFour_connected

/-- The hyperplane consisting of the two edges `{0,1}` and `{2,3}` of the four-cycle. -/
def cycleFourWall (a b : ZMod 4) : ZMod 2 :=
  if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) then 1 else 0

theorem cycleFourWall_square : ∀ a b c d : ZMod 4, cycleFourSq a b c d →
    cycleFourWall a b = cycleFourWall c d := by decide

theorem cycleFourWall_isWallLabel : cycleFour.IsWallLabel cycleFourWall where
  symm := by decide
  square := fun {a b c d} h => cycleFourWall_square a b c d h

/-- The general two-sidedness theorem applied to that hyperplane: it is the set of edges joining
the two sides of a partition of the vertices of the four-cycle. -/
theorem cycleFour_wall : ∃ σ : ZMod 4 → ZMod 2, σ 0 = 0 ∧
    ∀ u v : ZMod 4, cycleFour.adj u v → σ u + σ v = cycleFourWall u v :=
  SquareComplex.exists_side cycleFour_simplyConnected cycleFour_connected
    cycleFourWall_isWallLabel

/-- The second hyperplane of the four-cycle, consisting of the edges `{1,2}` and `{3,0}`. -/
def cycleFourWall' (a b : ZMod 4) : ZMod 2 :=
  if (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) ∨ (a = 3 ∧ b = 0) ∨ (a = 0 ∧ b = 3) then 1 else 0

/-- The two hyperplanes of the four-cycle, indexed by `Bool`. -/
def cycleFourWalls : Bool → ZMod 4 → ZMod 4 → ZMod 2
  | false => cycleFourWall
  | true => cycleFourWall'

theorem cycleFourWall'_square : ∀ a b c d : ZMod 4, cycleFourSq a b c d →
    cycleFourWall' a b = cycleFourWall' c d := by decide

theorem cycleFourWalls_edge_unique : ∀ u v : ZMod 4, cycleFourAdj u v →
    ∃ i : Bool, cycleFourWalls i u v = 1 ∧ ∀ j : Bool, cycleFourWalls j u v = 1 → j = i := by
  decide

/-- The two hyperplanes form a wall system on the four-cycle: every edge crosses exactly one of
them. -/
def cycleFourWallSystem : cycleFour.WallSystem Bool where
  χ := cycleFourWalls
  isWall := by
    intro i
    cases i with
    | false => exact cycleFourWall_isWallLabel
    | true => exact ⟨by decide, fun {a b c d} h => cycleFourWall'_square a b c d h⟩
  edge_unique := fun u v h => cycleFourWalls_edge_unique u v h

/-- The halfspace (Roller) coordinates produced by the general theorem for the four-cycle. -/
theorem cycleFour_rollerCoordinates :
    ∃ σ : Bool → ZMod 4 → ZMod 2,
      (∀ i, σ i 0 = 0) ∧
      (∀ (i : Bool) (u v : ZMod 4), cycleFour.adj u v → σ i u + σ i v = cycleFourWalls i u v) ∧
      (∀ v : ZMod 4, {i : Bool | σ i v ≠ σ i 0}.Finite) ∧
      (∀ u v : ZMod 4, cycleFour.adj u v → ∃ j : Bool, {i : Bool | σ i u ≠ σ i v} = {j}) :=
  SquareComplex.exists_rollerCoordinates cycleFour_simplyConnected cycleFour_connected
    cycleFourWallSystem

/-- The four-cycle *without* its two-cell. -/
def cycleFourNoSquare : SquareComplex (ZMod 4) where
  adj := cycleFourAdj
  adj_symm := fun {a b} h => cycleFourAdj_symm a b h
  adj_irrefl := cycleFourAdj_irrefl
  sq := fun _ _ _ _ => False
  sq_adj := fun h => h.elim
  sq_rotate := fun h => h
  sq_reverse := fun h => h

/-- Without two-cells every single edge is a wall on its own; here the edge `{0,1}`. -/
def cycleFourEdgeWall (a b : ZMod 4) : ZMod 2 :=
  if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then 1 else 0

theorem cycleFourNoSquare_wall : cycleFourNoSquare.IsWallLabel cycleFourEdgeWall where
  symm := by decide
  square := fun h => h.elim

theorem cycleFourNoSquare_closed : cycleFourNoSquare.IsClosedWalk 0 [0, 1, 2, 3, 0] :=
  ⟨(by decide : List.IsChain cycleFourAdj [0, 1, 2, 3, 0]), rfl, rfl⟩

/-- Without the two-cell the four-cycle is no longer simply connected: the loop
`0, 1, 2, 3, 0` crosses the wall consisting of the single edge `{0,1}` exactly once. -/
theorem cycleFourNoSquare_not_simplyConnected : ¬ cycleFourNoSquare.SimplyConnected := by
  intro hSC
  have h := SquareComplex.crossings_eq_zero_of_closed hSC cycleFourNoSquare_wall
    cycleFourNoSquare_closed
  revert h
  decide

end FiniteChains
