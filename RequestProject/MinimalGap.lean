import RequestProject.ComponentChain
import RequestProject.IdentityCover
import RequestProject.Consistency

/-!
# The minimal path to a complete proof of Theorem A

The implication `(1) ⇒ (2)` of Theorem A is proved in this project without any hypothesis
(`RequestProject/ComponentChain.lean`).  For the converse the project has so far carried the
whole geometric apparatus of Section 3 as an interface: `FiniteChains.RelativeInputs` (an
initial pair together with the operations `T` and `Q` and fifteen properties of them) and
`FiniteChains.SufficiencyInputs`.  This file cuts that interface down to what is logically
indispensable and checks the reduction in Lean.

What remains unproved is exactly **two** statements:

* `step` — *relative chains extend*: over an acyclic complex `D`, a chain
  `D = L₀ ⊊ ⋯ ⊊ Lₙ` of Cockcroft complexes with inclusions zero on `π₂` and with `π₁(D)`
  dying from the first stage on can always be prolonged by one term.  This is the content of
  Lemma 3.1 (the case `n = 0`) and of Lemmas 3.9–3.10 (the inductive step);
* `descent` — Proposition 3.11: such a chain over a connected acyclic regular cover `D` of
  `K` descends to a chain over `K` whose inclusions are zero on `π₂`.

Everything else — the whole induction of Proposition 3.7, the derivation of `(1) ⇒ (2)`, and
the fact that an acyclic complex is Cockcroft — is proved here.

* `FiniteChains.MinimalSufficiency` — the two statements above, as an interface;
* `FiniteChains.minimalSufficiency_of_sufficiencyInputs` — the old, much larger interface
  implies the minimal one, so nothing is lost by the reduction;
* `FiniteChains.exists_relativeChain_of_minimal`, `FiniteChains.hasZeroChains_of_minimal`,
  `FiniteChains.theoremA_of_minimal` — Theorem A from the minimal interface;
* `FiniteChains.Comb.isCockcroft_of_isAcyclic` — an acyclic two-complex is Cockcroft (this
  was a hypothesis of `RelativeInputs`; it is a theorem);
* `FiniteChains.Comb.Gap` and `FiniteChains.Comb.theoremA_of_gap` — **Theorem A for finite
  connected combinatorial two-complexes, proved from exactly those two geometric
  statements**.
-/

namespace FiniteChains

universe u

variable {W : TwoComplexData.{u}}

/-! ### The minimal interface -/

/-- **The minimal geometric input for `(2) ⇒ (1)`.**  Compared with
`FiniteChains.SufficiencyInputs` the replacement operation `T`, the terminal extension `Q`
and their fifteen properties are replaced by the single statement that a relative chain can
be prolonged by one term, and the descent is only asked to produce a chain which is zero on
`π₂` (its terms need not be Cockcroft). -/
structure MinimalSufficiency (W : TwoComplexData.{u}) : Prop where
  /-- An acyclic complex is Cockcroft.  (A theorem in the combinatorial model, see
  `FiniteChains.Comb.isCockcroft_of_isAcyclic`.) -/
  cockcroft_of_acyclic : ∀ D, W.Acyclic D → W.Cockcroft D
  /-- The total space of an acyclic cover is acyclic. -/
  acyclic_of_cover : ∀ D K, W.IsAcyclicCover D K → W.Acyclic D
  /-- **Lemmas 3.1, 3.9 and 3.10:** a relative chain over an acyclic complex extends. -/
  step : ∀ D, W.Acyclic D → ∀ (c : ℕ → W.Cx) (n : ℕ), IsRelativeChain W D c n →
      ∃ c' : ℕ → W.Cx, IsRelativeChain W D c' (n + 1)
  /-- **Proposition 3.11:** a relative chain over an acyclic regular cover of `K` descends to
  a chain over `K` whose inclusions are zero on `π₂`. -/
  descent : ∀ (K D : W.Cx) (c : ℕ → W.Cx) (n : ℕ), W.IsAcyclicCover D K →
      IsRelativeChain W D c n → ∃ e : ℕ → W.Cx, e 0 = K ∧ IsZeroChain W e n

/-- The constant chain of length zero over a Cockcroft complex. -/
theorem isRelativeChain_const {D : W.Cx} (hD : W.Cockcroft D) :
    IsRelativeChain W D (fun _ => D) 0 :=
  ⟨⟨fun i hi => absurd hi (Nat.not_lt_zero i), fun i hi => absurd hi (Nat.not_lt_zero i),
      fun i hi => absurd hi (Nat.not_lt_zero i)⟩,
    rfl, fun _ _ => hD, fun i h1 h2 => absurd h1 (by omega)⟩

/-- **Proposition 3.7 from the single extension step.**  Over an acyclic complex there are
relative chains of every finite length. -/
theorem exists_relativeChain_of_minimal (h : MinimalSufficiency W) {D : W.Cx}
    (hD : W.Acyclic D) : ∀ n : ℕ, ∃ c : ℕ → W.Cx, IsRelativeChain W D c n := by
  intro n
  induction n with
  | zero => exact ⟨fun _ => D, isRelativeChain_const (h.cockcroft_of_acyclic D hD)⟩
  | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      exact h.step D hD c n hc

/-- **`(2) ⇒ (1)` of Theorem A from the minimal interface.** -/
theorem hasZeroChains_of_minimal (h : MinimalSufficiency W) {K : W.Cx}
    (hK : HasAcyclicRegularCover W K) : HasZeroChains W K := by
  obtain ⟨D, hD⟩ := hK
  intro n
  obtain ⟨c, hc⟩ := exists_relativeChain_of_minimal h (h.acyclic_of_cover D K hD) n
  exact h.descent K D c n hD hc

/-- **Theorem A from the minimal interface.** -/
theorem theoremA_of_minimal (h : MinimalSufficiency W) {K : W.Cx} (J : NecessityInputs W K) :
    HasZeroChains W K ↔ HasAcyclicRegularCover W K :=
  ⟨fun hc => hasAcyclicRegularCover_of_hasZeroChains J hc, fun hc => hasZeroChains_of_minimal h hc⟩

/-- **The reduction loses nothing:** the interface of Section 3 used so far implies the
minimal one. -/
theorem minimalSufficiency_of_sufficiencyInputs (I : SufficiencyInputs W) :
    MinimalSufficiency W where
  cockcroft_of_acyclic D hD := (I.rel D hD).cockcroft_core
  acyclic_of_cover := I.acyclic_of_cover
  step D hD c n hc := by
    match n with
    | 0 =>
        -- the initial pair of Lemma 3.1
        refine ⟨fun i => if i = 0 then D else (I.rel D hD).Y, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
        · intro i hi
          interval_cases i
          simpa using (I.rel D hD).sub_Y
        · intro i hi
          interval_cases i
          simpa using (I.rel D hD).ne_Y
        · intro i hi
          interval_cases i
          simpa using (I.rel D hD).zero_Y
        · simp
        · intro i hi
          interval_cases i
          · simpa using (I.rel D hD).cockcroft_core
          · simpa using (I.rel D hD).cockcroft_Y
        · intro i hi1 hi2
          interval_cases i
          simpa using (I.rel D hD).pi1_Y
    | (m + 1) => exact ⟨_, relativeChain_step (I.rel D hD) hc⟩
  descent K D c n hcov hc := by
    obtain ⟨e, he0, hz, -⟩ := I.descent K D c n hcov hc
    exact ⟨e, he0, hz⟩

/-- **The minimal interface is consistent**: it holds in the toy model of
`RequestProject/Consistency.lean`, so the implications above are not vacuous. -/
theorem toyMinimalSufficiency : MinimalSufficiency toyData :=
  minimalSufficiency_of_sufficiencyInputs toySufficiencyInputs

/-! ### The minimal path in the combinatorial model -/

namespace Comb

variable {X : Complex2.{u}}

/-- **An acyclic two-complex is Cockcroft.**  A two-cycle of the universal cover projects to
a two-cycle of the complex, and an acyclic complex has none but zero.  (In
`FiniteChains.RelativeInputs` this was a hypothesis.) -/
theorem isCockcroft_of_isAcyclic (h : IsAcyclic X) : IsCockcroft X := by
  intro x₀ c hc
  refine h.h2 ?_
  rw [bdry2_hurewicz hc, map_zero]

/-- Condition (1) of Theorem A with finite stages: the form in which the machinery of
Section 2 consumes it. -/
def HasFiniteZeroChains (K : Complex2.{u}) : Prop :=
  ∀ n : ℕ, ∃ c : ℕ → Complex2.{u}, c 0 = K ∧ IsZeroChain combData c n ∧
    (∀ i, i ≤ n → Finite (c i).E) ∧ (∀ i, i ≤ n → Finite (c i).F)

/-- **The two statements that are still missing for a complete proof of Theorem A.**  Both
are statements of Section 3 of the paper about honest combinatorial two-complexes; every
other ingredient of Theorem A is proved in this project. -/
structure Gap : Prop where
  /-- **Lemmas 3.1, 3.9, 3.10.**  Over an acyclic complex `D`, a chain `D = L₀ ⊊ ⋯ ⊊ Lₙ` of
  Cockcroft complexes whose inclusions are zero on `π₂` and in which `π₁(D)` dies from the
  first stage on can be prolonged by one term. -/
  step : ∀ D : Complex2.{u}, IsAcyclic D → ∀ (c : ℕ → Complex2.{u}) (n : ℕ),
      IsRelativeChain combData D c n → ∃ c' : ℕ → Complex2.{u}, IsRelativeChain combData D c' (n + 1)
  /-- **Proposition 3.11.**  Such a chain over a connected acyclic regular cover `D` of a
  finite complex `K` descends to a chain over `K` with finite stages whose inclusions are
  zero on `π₂`.  (The stages are finite because the pushout `K ∪_D Lᵢ` adds to `K` only the
  cells of `Lᵢ` outside `D`, of which the construction produces finitely many.) -/
  descent : ∀ (K D : Complex2.{u}) (c : ℕ → Complex2.{u}) (n : ℕ), IsAcyclicCover D K →
      IsRelativeChain combData D c n → Finite K.E → Finite K.F →
      ∃ e : ℕ → Complex2.{u}, e 0 = K ∧ IsZeroChain combData e n ∧
        (∀ i, i ≤ n → Finite (e i).E) ∧ (∀ i, i ≤ n → Finite (e i).F)

/-- **`(2) ⇒ (1)` for finite combinatorial two-complexes, from the two missing statements.**
-/
theorem hasFiniteZeroChains_of_gap (g : Gap.{u}) {K : Complex2.{u}} [Finite K.E] [Finite K.F]
    (hK : HasAcyclicRegularCover K) : HasFiniteZeroChains K := by
  obtain ⟨D, Q, hQ, p, A, hcov, hreg, hconnD, hacycD⟩ := hK
  have hcover : IsAcyclicCover D K := ⟨Q, hQ, p, A, hcov, hreg, hconnD, hacycD⟩
  intro n
  have hchain : ∀ m : ℕ, ∃ c : ℕ → Complex2.{u}, IsRelativeChain combData D c m := by
    intro m
    induction m with
    | zero => exact ⟨fun _ => D, isRelativeChain_const (isCockcroft_of_isAcyclic hacycD)⟩
    | succ m ih =>
        obtain ⟨c, hc⟩ := ih
        exact g.step D hacycD c m hc
  obtain ⟨c, hc⟩ := hchain n
  obtain ⟨e, he0, hz, hfE, hfF⟩ := g.descent K D c n hcover hc inferInstance inferInstance
  exact ⟨e, he0, hz, hfE, hfF⟩

/-- **Theorem A for finite connected combinatorial two-complexes, modulo exactly the two
statements of `FiniteChains.Comb.Gap`.**  The implication `(1) ⇒ (2)` is a theorem of this
project; the converse is the content of the gap. -/
theorem theoremA_of_gap (g : Gap.{u}) {K : Complex2.{u}} [Finite K.E] [Finite K.F]
    (hconn : IsConnected K) (x₀ : K.V) :
    HasFiniteZeroChains K ↔ HasAcyclicRegularCover K :=
  ⟨fun h => hasAcyclicRegularCover_of_hasZeroChains_comb_disc hconn x₀ h,
    fun h => hasFiniteZeroChains_of_gap g h⟩

/-- Non-vacuity of the reduction: for an acyclic finite connected complex both sides hold
unconditionally — condition (2) by the identity cover, and hence condition (1) as soon as the
gap is filled. -/
theorem hasAcyclicRegularCover_of_isAcyclic' {K : Complex2.{u}} (hconn : IsConnected K)
    (hacyc : IsAcyclic K) : HasAcyclicRegularCover K :=
  hasAcyclicRegularCover_of_isAcyclic hconn hacyc

end Comb
end FiniteChains
