import RequestProject.Framework

/-!
# The finiteness supplement of Theorem A

Theorem A of the paper carries a supplementary assertion: *if `K` is finite and acyclic, then
all the members of the chains in (1) can be chosen finite.*  This file formalises it in the
same framework as `RequestProject/Framework.lean`.

Finiteness of a complex is an extra predicate `Fin` on the complexes, and the geometric input
is that the construction of Lemma 3.1 and the two operations `T` and `Q` of Section 3.4 keep a
complex finite — which is clear from their definitions, since each of them attaches finitely
many cells to a finite complex.  Under that input the construction of relative chains
(Proposition 3.7) produces chains with all terms finite:

* `FiniteChains.FinitenessInputs` — the finiteness input;
* `FiniteChains.exists_relativeChain_finite` — relative chains of every length whose terms are
  all finite;
* `FiniteChains.hasFiniteCockcroftZeroChains_of_acyclic` — for a finite acyclic `K` (which is
  its own acyclic regular cover) this gives chains as in (1) of Theorem A all of whose terms
  are finite and Cockcroft.
-/

namespace FiniteChains

universe u

variable {W : TwoComplexData.{u}}

/-- The finiteness input: a predicate `Fin` on complexes which holds for the acyclic core `D`
and for the complex `Y_D` of Lemma 3.1, and which is preserved by the replacement operation
`T` and by the terminal extension `Q`. -/
structure FinitenessInputs {D : W.Cx} (h : RelativeInputs W D) where
  /-- `Fin P` : the complex `P` is finite. -/
  Fin : W.Cx → Prop
  /-- The acyclic core is finite. -/
  fin_core : Fin D
  /-- The complex `Y_D` of Lemma 3.1 is finite. -/
  fin_Y : Fin h.Y
  /-- `T` attaches finitely many cells. -/
  fin_repl : ∀ P, Fin P → Fin (h.repl P)
  /-- `Q` attaches finitely many cells. -/
  fin_term : ∀ P, Fin P → Fin (h.term P)

/-- **Proposition 3.7 with finiteness.**  Over a finite acyclic core the relative chains of
every finite length can be chosen with all terms finite. -/
theorem exists_relativeChain_finite {D : W.Cx} (h : RelativeInputs W D)
    (F : FinitenessInputs h) :
    ∀ n : ℕ, ∃ c : ℕ → W.Cx, IsRelativeChain W D c n ∧ ∀ i ≤ n, F.Fin (c i) := by
  have key : ∀ n : ℕ, ∃ c : ℕ → W.Cx, IsRelativeChain W D c (n + 1) ∧ ∀ i ≤ n + 1, F.Fin (c i) := by
    intro n
    induction n with
    | zero =>
        refine ⟨fun i => if i = 0 then D else h.Y, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
        · intro i hi
          interval_cases i
          simpa using h.sub_Y
        · intro i hi
          interval_cases i
          simpa using h.ne_Y
        · intro i hi
          interval_cases i
          simpa using h.zero_Y
        · simp
        · intro i hi
          interval_cases i
          · simpa using h.cockcroft_core
          · simpa using h.cockcroft_Y
        · intro i hi1 hi2
          interval_cases i
          simpa using h.pi1_Y
        · intro i hi
          interval_cases i
          · simpa using F.fin_core
          · simpa using F.fin_Y
    | succ n ih =>
        obtain ⟨c, hc, hfin⟩ := ih
        refine ⟨fun i => if i ≤ n + 1 then h.repl (c i) else h.term (c (n + 1)), ?_, ?_⟩
        · exact relativeChain_step h hc
        · intro i hi
          rcases Nat.lt_or_ge i (n + 2) with h' | h'
          · simp only [if_pos (by omega : i ≤ n + 1)]
            exact F.fin_repl _ (hfin i (by omega))
          · have hi2 : i = n + 2 := by omega
            subst hi2
            simp only [if_neg (by omega : ¬ (n + 2 ≤ n + 1))]
            exact F.fin_term _ (hfin (n + 1) le_rfl)
  intro n
  match n with
  | 0 =>
      refine ⟨fun _ => D,
        ⟨⟨fun i hi => absurd hi (Nat.not_lt_zero i), fun i hi => absurd hi (Nat.not_lt_zero i),
          fun i hi => absurd hi (Nat.not_lt_zero i)⟩,
          rfl, fun _ _ => h.cockcroft_core, fun i hi1 hi2 => absurd hi2 (by omega)⟩, ?_⟩
      intro i _
      exact F.fin_core
  | (n + 1) => exact key n

/-- Condition (1) of Theorem A together with the supplementary assertions that all terms of the
chains can be chosen Cockcroft **and finite**. -/
def HasFiniteCockcroftZeroChains (W : TwoComplexData) (Fin : W.Cx → Prop) (K : W.Cx) : Prop :=
  ∀ n : ℕ, ∃ c : ℕ → W.Cx, c 0 = K ∧ IsZeroChain W c n ∧ (∀ i ≤ n, W.Cockcroft (c i)) ∧
    ∀ i ≤ n, Fin (c i)

/-- **The finiteness supplement of Theorem A.**  A finite acyclic complex is its own acyclic
regular cover, so the relative chains of Proposition 3.7 already start at `K`: all their terms
are finite and Cockcroft, and all inclusions are zero on `π₂`. -/
theorem hasFiniteCockcroftZeroChains_of_acyclic {K : W.Cx} (h : RelativeInputs W K)
    (F : FinitenessInputs h) : HasFiniteCockcroftZeroChains W F.Fin K := by
  intro n
  obtain ⟨c, hc, hfin⟩ := exists_relativeChain_finite h F n
  exact ⟨c, hc.base, hc.toIsZeroChain, hc.cockcroft, hfin⟩

end FiniteChains
