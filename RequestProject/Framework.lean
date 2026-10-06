module

public import RequestProject.Pigeonhole
public import RequestProject.SubgroupCompactness

@[expose] public section

/-!
# Theorem A: the formal skeleton

Theorem A of the paper reads: for a connected two-complex `K` the following are
equivalent.

1. For every `n ≥ 1` there is a chain `K = K₀ ⊊ K₁ ⊊ ⋯ ⊊ Kₙ` of two-complexes
   in which every inclusion induces zero on `π₂`.
2. `K` has a connected acyclic regular cover.

Homotopy theory of two-complexes (`π₁`, `π₂`, Hurewicz, covering spaces, the
CAT(0) cube complexes behind the blocks `B_q`) is far outside what can be built
here, so the notions occurring in Theorem A are packaged in the interface
`TwoComplexData`, and the geometric statements proved in the paper are recorded
as explicit hypotheses:

* `RelativeInputs` records Lemma 3.1 (the initial Cockcroft pair `D ⊂ Y_D`)
  together with the properties of the replacement operation `T` and its
  terminal extension `Q` established in Lemmas 3.9 and 3.10;
* `SufficiencyInputs` adds the descent step, Proposition 3.11;
* `NecessityInputs` records the Fox-boundary input of Section 2, namely
  formula (2.3) relating a chain to normal subgroups of `G = π₁(K)`, the finite
  determinacy of the requirements, their stability under intersections of
  chains, Lemma 2.1 in the form "the commutator subgroup inherits the
  requirements", and the identification of an acyclic regular cover with a
  perfect normal subgroup satisfying them.

What *is* proved here is the entire bookkeeping of the paper's two inductions:
the construction of relative chains of arbitrary length from the operations `T`
and `Q` (Proposition 3.7), the descent to `K` (so `(2) ⇒ (1)`), and the
pigeonhole/compactness/minimality derivation of a perfect normal subgroup from
chains of every finite length (so `(1) ⇒ (2)`).
-/

namespace FiniteChains

universe u

/-- The notions of Theorem A, as an abstract interface. -/
structure TwoComplexData where
  /-- The two-complexes under consideration. -/
  Cx : Type u
  /-- `Sub K L` : `K` is a subcomplex of `L` (all cells of `K` are retained). -/
  Sub : Cx → Cx → Prop
  sub_refl : ∀ K, Sub K K
  sub_trans : ∀ {K L M}, Sub K L → Sub L M → Sub K M
  /-- The Hurewicz map of the complex vanishes. -/
  Cockcroft : Cx → Prop
  /-- `ZeroPi2 K L` : the inclusion `K ⊆ L` induces the zero map on `π₂`. -/
  ZeroPi2 : Cx → Cx → Prop
  /-- `Pi1Trivial K L` : the map `π₁(K) → π₁(L)` is trivial. -/
  Pi1Trivial : Cx → Cx → Prop
  /-- The complex is acyclic. -/
  Acyclic : Cx → Prop
  /-- `IsAcyclicCover D K` : `D` is a connected acyclic regular cover of `K`. -/
  IsAcyclicCover : Cx → Cx → Prop

variable (W : TwoComplexData)

/-- A chain `c 0 ⊊ c 1 ⊊ ⋯ ⊊ c n` all of whose inclusions are zero on `π₂`: condition (1)
of Theorem A. -/
structure IsZeroChain (c : ℕ → W.Cx) (n : ℕ) : Prop where
  sub : ∀ i < n, W.Sub (c i) (c (i + 1))
  strict : ∀ i < n, c i ≠ c (i + 1)
  zero : ∀ i < n, W.ZeroPi2 (c i) (c (i + 1))

/-- The chains produced by Proposition 3.7: a chain over the fixed acyclic core `D`, with
all terms Cockcroft and with `π₁(D)` killed from the first step on. -/
structure IsRelativeChain (D : W.Cx) (c : ℕ → W.Cx) (n : ℕ) : Prop extends IsZeroChain W c n where
  base : c 0 = D
  cockcroft : ∀ i ≤ n, W.Cockcroft (c i)
  pi1 : ∀ i, 1 ≤ i → i ≤ n → W.Pi1Trivial D (c i)

/-- Condition (2) of Theorem A. -/
def HasAcyclicRegularCover (K : W.Cx) : Prop := ∃ D, W.IsAcyclicCover D K

/-- Condition (1) of Theorem A. -/
def HasZeroChains (K : W.Cx) : Prop :=
  ∀ n : ℕ, ∃ c : ℕ → W.Cx, c 0 = K ∧ IsZeroChain W c n

/-- Condition (1) of Theorem A together with the supplementary assertion that all terms of
the chains can be chosen Cockcroft. -/
def HasCockcroftZeroChains (K : W.Cx) : Prop :=
  ∀ n : ℕ, ∃ c : ℕ → W.Cx, c 0 = K ∧ IsZeroChain W c n ∧ ∀ i ≤ n, W.Cockcroft (c i)

/-!
## Input from Section 3: the replacement operation and its terminal extension
-/

/-- The geometric input of Section 3 over a fixed acyclic core `D`: the initial Cockcroft
pair of Lemma 3.1, and the operations `T` (replacement) and `Q` (terminal extension) with
the properties established in Lemmas 3.9 and 3.10. -/
structure RelativeInputs (D : W.Cx) where
  /-- `D` is acyclic, hence Cockcroft. -/
  cockcroft_core : W.Cockcroft D
  /-- The complex `Y_D` of Lemma 3.1. -/
  Y : W.Cx
  sub_Y : W.Sub D Y
  ne_Y : D ≠ Y
  cockcroft_Y : W.Cockcroft Y
  zero_Y : W.ZeroPi2 D Y
  pi1_Y : W.Pi1Trivial D Y
  /-- The replacement operation `T` of Section 3.4. -/
  repl : W.Cx → W.Cx
  /-- The terminal extension `Q` of Section 3.4. -/
  term : W.Cx → W.Cx
  /-- `T(D) = D`: the core is retained literally. -/
  repl_core : repl D = D
  /-- `T` respects labelled inclusions. -/
  repl_mono : ∀ P P', W.Sub P P' → W.Sub (repl P) (repl P')
  /-- Strictness is preserved (fresh generators and fresh block lists). -/
  repl_strict : ∀ P P', W.Sub P P' → P ≠ P' → repl P ≠ repl P'
  /-- `T` preserves Cockcroftness (Lemma 3.9). -/
  repl_cockcroft : ∀ P, W.Cockcroft P → W.Cockcroft (repl P)
  /-- `T` preserves zero maps on `π₂` (Lemma 3.9). -/
  repl_zero : ∀ P P', W.Sub P P' → W.ZeroPi2 P P' → W.ZeroPi2 (repl P) (repl P')
  /-- `T` preserves the triviality of the core group. -/
  repl_pi1 : ∀ P, W.Pi1Trivial D P → W.Pi1Trivial D (repl P)
  /-- `Q(P)` literally extends `T(P)` (Lemma 3.10). -/
  sub_term : ∀ P, W.Cockcroft P → W.Pi1Trivial D P → W.Sub (repl P) (term P)
  ne_term : ∀ P, W.Cockcroft P → W.Pi1Trivial D P → repl P ≠ term P
  /-- `Q(P)` is Cockcroft (Lemma 3.10). -/
  cockcroft_term : ∀ P, W.Cockcroft P → W.Pi1Trivial D P → W.Cockcroft (term P)
  /-- `T(P) ⊂ Q(P)` is zero on `π₂` (Lemma 3.10). -/
  zero_term : ∀ P, W.Cockcroft P → W.Pi1Trivial D P → W.ZeroPi2 (repl P) (term P)
  /-- The core group stays trivial in `Q(P)`. -/
  pi1_term : ∀ P, W.Pi1Trivial D P → W.Pi1Trivial D (term P)

variable {W}

/-- The induction step of Proposition 3.7 (step (3.9) of the paper): apply the replacement
operation `T` to every term of a relative chain and append the terminal extension `Q` of its
last term. -/
theorem relativeChain_step {D : W.Cx} (h : RelativeInputs W D) {c : ℕ → W.Cx} {n : ℕ}
    (hc : IsRelativeChain W D c (n + 1)) :
    IsRelativeChain W D
      (fun i => if i ≤ n + 1 then h.repl (c i) else h.term (c (n + 1))) (n + 2) := by
  have hcock : W.Cockcroft (c (n + 1)) := hc.cockcroft _ le_rfl
  have hpi1 : W.Pi1Trivial D (c (n + 1)) := hc.pi1 _ (by omega) le_rfl
  constructor
  · constructor
    · intro i hi
      rcases Nat.lt_or_ge i (n + 1) with h' | h'
      · simp only [if_pos (by omega : i ≤ n + 1), if_pos (by omega : i + 1 ≤ n + 1)]
        exact h.repl_mono _ _ (hc.sub i h')
      · have : i = n + 1 := by omega
        subst this
        simp only [if_pos (le_refl (n + 1)), if_neg (by omega : ¬ (n + 1 + 1 ≤ n + 1))]
        exact h.sub_term _ hcock hpi1
    · intro i hi
      rcases Nat.lt_or_ge i (n + 1) with h' | h'
      · simp only [if_pos (by omega : i ≤ n + 1), if_pos (by omega : i + 1 ≤ n + 1)]
        exact h.repl_strict _ _ (hc.sub i h') (hc.strict i h')
      · have : i = n + 1 := by omega
        subst this
        simp only [if_pos (le_refl (n + 1)), if_neg (by omega : ¬ (n + 1 + 1 ≤ n + 1))]
        exact h.ne_term _ hcock hpi1
    · intro i hi
      rcases Nat.lt_or_ge i (n + 1) with h' | h'
      · simp only [if_pos (by omega : i ≤ n + 1), if_pos (by omega : i + 1 ≤ n + 1)]
        exact h.repl_zero _ _ (hc.sub i h') (hc.zero i h')
      · have : i = n + 1 := by omega
        subst this
        simp only [if_pos (le_refl (n + 1)), if_neg (by omega : ¬ (n + 1 + 1 ≤ n + 1))]
        exact h.zero_term _ hcock hpi1
  · simp only [if_pos (Nat.zero_le _), hc.base, h.repl_core]
  · intro i hi
    rcases Nat.lt_or_ge i (n + 2) with h' | h'
    · simp only [if_pos (by omega : i ≤ n + 1)]
      exact h.repl_cockcroft _ (hc.cockcroft i (by omega))
    · have : i = n + 2 := by omega
      subst this
      simp only [if_neg (by omega : ¬ (n + 2 ≤ n + 1))]
      exact h.cockcroft_term _ hcock hpi1
  · intro i hi1 hi2
    rcases Nat.lt_or_ge i (n + 2) with h' | h'
    · simp only [if_pos (by omega : i ≤ n + 1)]
      exact h.repl_pi1 _ (hc.pi1 i hi1 (by omega))
    · have : i = n + 2 := by omega
      subst this
      simp only [if_neg (by omega : ¬ (n + 2 ≤ n + 1))]
      exact h.pi1_term _ hpi1

/-- **Proposition 3.7.**  From the initial pair and the two operations one gets relative
chains of every finite length over the acyclic core `D`. -/
theorem exists_relativeChain {D : W.Cx} (h : RelativeInputs W D) :
    ∀ n : ℕ, ∃ c : ℕ → W.Cx, IsRelativeChain W D c n := by
  -- First the chains of positive length, by induction on the number of inclusions.
  have key : ∀ n : ℕ, ∃ c : ℕ → W.Cx, IsRelativeChain W D c (n + 1) := by
    intro n
    induction n with
    | zero =>
        refine ⟨fun i => if i = 0 then D else h.Y, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
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
    | succ n ih =>
        obtain ⟨c, hc⟩ := ih
        exact ⟨_, relativeChain_step h hc⟩
  intro n
  match n with
  | 0 =>
      exact ⟨fun _ => D,
        ⟨fun i hi => absurd hi (Nat.not_lt_zero i), fun i hi => absurd hi (Nat.not_lt_zero i),
          fun i hi => absurd hi (Nat.not_lt_zero i)⟩,
        rfl, fun _ _ => h.cockcroft_core, fun i hi1 hi2 => absurd hi2 (by omega)⟩
  | (n + 1) => exact key n

variable (W)

/-- The remaining input for `(2) ⇒ (1)`: relative chains exist over any acyclic complex,
acyclic covers are acyclic, and the descent of Proposition 3.11. -/
structure SufficiencyInputs where
  rel : ∀ D : W.Cx, W.Acyclic D → RelativeInputs W D
  acyclic_of_cover : ∀ D K : W.Cx, W.IsAcyclicCover D K → W.Acyclic D
  /-- **Proposition 3.11**: a relative chain over an acyclic regular cover `D` of `K`
  descends to a chain of Cockcroft complexes over `K` with all maps zero on `π₂`. -/
  descent : ∀ (K D : W.Cx) (c : ℕ → W.Cx) (n : ℕ), W.IsAcyclicCover D K →
      IsRelativeChain W D c n →
      ∃ e : ℕ → W.Cx, e 0 = K ∧ IsZeroChain W e n ∧ ∀ i ≤ n, W.Cockcroft (e i)

variable {W}

/-- **`(2) ⇒ (1)` of Theorem A**, including the assertion that all terms can be chosen
Cockcroft. -/
theorem hasCockcroftZeroChains_of_hasAcyclicRegularCover (I : SufficiencyInputs W) {K : W.Cx}
    (hK : HasAcyclicRegularCover W K) : HasCockcroftZeroChains W K := by
  obtain ⟨D, hD⟩ := hK
  intro n
  obtain ⟨c, hc⟩ := exists_relativeChain (I.rel D (I.acyclic_of_cover D K hD)) n
  exact I.descent K D c n hD hc

/-!
## Input from Section 2: Fox boundaries and the requirements (2.2)
-/

/-- The input of Section 2 for a fixed complex `K`.  `Req` indexes the requirements (2.2),
one for each finitely supported coefficient vector, integrally and modulo every prime;
`Sat N v` says that the requirement `v` holds for the normal subgroup `N`, i.e. that the
Fox boundary `∂_{2,N}` does not kill `v`. -/
structure NecessityInputs (W : TwoComplexData) (K : W.Cx) where
  /-- The fundamental group `G = π₁(K)`. -/
  G : Type u
  grp : Group G
  /-- The requirements (2.2). -/
  Req : Type u
  /-- `Sat N v` : the requirement `v` is satisfied by the normal subgroup `N`. -/
  Sat : @Subgroup G grp → Req → Prop
  /-- **Formula (2.3)**: a chain of `n` inclusions starting at `K` supplies `n+1` normal
  subgroups of `G` such that a requirement failing at one stage holds at all later
  stages. -/
  chain_subgroups : ∀ (c : ℕ → W.Cx) (n : ℕ), c 0 = K → IsZeroChain W c n →
      ∃ M : ℕ → @Subgroup G grp, (∀ r, @Subgroup.Normal G grp (M r)) ∧
        ∀ r v, ¬ Sat (M r) v → ∀ s, r < s → s ≤ n → Sat (M s) v
  /-- Each requirement depends on finitely many decisions `g ∈ M`.  For the Fox
  requirements this is proved in `FoxRequirement.lean`
  (`FiniteChains.foxSat_finitelyDetermined`). -/
  det : @FinitelyDetermined G grp Req Sat
  /-- Requirements pass to intersections of decreasing chains of normal subgroups. -/
  sat_sInf_chain : ∀ C : Set (@Subgroup G grp), IsChain (· ≤ ·) C → C.Nonempty →
      (∀ N ∈ C, @Subgroup.Normal G grp N ∧ ∀ v, Sat N v) → ∀ v, Sat (sInf C) v
  /-- **Lemma 2.1**: if `N` satisfies all requirements then so does `[N, N]`.  For the Fox
  requirements this is proved in `FoxCommutator.lean`
  (`FiniteChains.foxSat_commutator_forall`), assuming only that `N/[N, N]` is torsion
  free. -/
  sat_commutator : ∀ N : @Subgroup G grp, @Subgroup.Normal G grp N → (∀ v, Sat N v) →
      ∀ v, Sat ⁅N, N⁆ v
  /-- A perfect normal subgroup satisfying all requirements yields the acyclic regular
  cover `K_N`: `H₁(K_N) = N/[N,N] = 0` and `H₂(K_N) = ker ∂_{2,N} = 0`. -/
  cover_of_perfect : ∀ N : @Subgroup G grp, @Subgroup.Normal G grp N → (∀ v, Sat N v) →
      ⁅N, N⁆ = N → HasAcyclicRegularCover W K

/-- **`(1) ⇒ (2)` of Theorem A.**  Chains of every finite length produce, by the
one-violation principle, a normal subgroup meeting any finite set of requirements; the
compactness and minimality steps then produce a minimal such subgroup, and Lemma 2.1 makes
it perfect. -/
theorem hasAcyclicRegularCover_of_hasZeroChains {K : W.Cx} (J : NecessityInputs W K)
    (h : HasZeroChains W K) : HasAcyclicRegularCover W K := by
  classical
  letI := J.grp
  -- Step 1: any finite family of requirements is satisfied by a single normal subgroup.
  have hfin : ∀ S : Finset J.Req, ∃ N : Subgroup J.G, N.Normal ∧ ∀ v ∈ S, J.Sat N v := by
    intro S
    obtain ⟨c, hc0, hc⟩ := h S.card
    obtain ⟨M, hMnormal, hMlater⟩ := J.chain_subgroups c S.card hc0 hc
    obtain ⟨r, _, hr⟩ :=
      exists_stage_satisfying_all S le_rfl (fun r v => J.Sat (M r) v) hMlater
    exact ⟨M r, hMnormal r, hr⟩
  -- Step 2: compactness.
  obtain ⟨M, hMnormal, hM⟩ := exists_normal_subgroup_forall J.Sat J.det hfin
  -- Step 3: a minimal normal subgroup satisfying all requirements.
  obtain ⟨N, -, hNnormal, hN, hNmin⟩ :=
    exists_minimal_normal_sat (fun N => ∀ v, J.Sat N v)
      (fun C hchain hne hC => J.sat_sInf_chain C hchain hne hC) M hMnormal hM
  -- Step 4: Lemma 2.1 and minimality make `N` perfect.
  have hcomm : (⁅N, N⁆ : Subgroup J.G).Normal := by
    haveI := hNnormal
    infer_instance
  have hperfect : ⁅N, N⁆ = N :=
    hNmin ⁅N, N⁆ (Subgroup.commutator_le_left N N) hcomm (J.sat_commutator N hNnormal hN)
  exact J.cover_of_perfect N hNnormal hN hperfect

/-- **Theorem A** (equivalence of (1) and (2)), relative to the stated geometric input. -/
theorem theoremA (I : SufficiencyInputs W) {K : W.Cx} (J : NecessityInputs W K) :
    HasZeroChains W K ↔ HasAcyclicRegularCover W K := by
  refine ⟨fun h => hasAcyclicRegularCover_of_hasZeroChains J h, fun h n => ?_⟩
  obtain ⟨c, hc0, hc, -⟩ := hasCockcroftZeroChains_of_hasAcyclicRegularCover I h n
  exact ⟨c, hc0, hc⟩

/-- The supplementary assertion of Theorem A: when the conditions hold, all terms of the
chains in (1) can be chosen Cockcroft. -/
theorem theoremA_cockcroft (I : SufficiencyInputs W) {K : W.Cx} (J : NecessityInputs W K)
    (h : HasZeroChains W K) : HasCockcroftZeroChains W K :=
  hasCockcroftZeroChains_of_hasAcyclicRegularCover I
    (hasAcyclicRegularCover_of_hasZeroChains J h)

end FiniteChains
