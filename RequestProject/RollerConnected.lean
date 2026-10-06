import RequestProject.CubeRollerModel

/-!
# One-coordinate paths in the Roller model

`RequestProject/CubeRollerModel.lean` derives the descending-cube axioms — and hence the
vanishing of the second homology of the cellular chains — from a vertex set `W` of finite sets
of hyperplanes which contains the base vertex `∅` and is closed under the median (majority)
operation.

Closedness under the median is *not* by itself enough for `W` to be the vertex set of a graph
in which every step changes one coordinate.  The set

  `W = {∅, {p, q}}`   (`p ≠ q`)

is closed under the majority operation and contains the base vertex, but its two vertices
differ in two coordinates and no vertex of `W` lies between them, so there is no path from one
to the other changing one coordinate at a time (`FiniteChains.pairModel_not_stepConnected`).

This file therefore isolates the missing hypothesis and proves what it gives:

* `FiniteChains.OneStep` — a single move inside `W` changing exactly one coordinate;
* `FiniteChains.StepPath` — a path of such moves, with its length;
* `FiniteChains.ConnectedRollerModel` — a Roller model with the extra hypothesis that every
  vertex other than the base vertex has a *descending* neighbour inside `W` (some coordinate
  can be removed without leaving `W`);
* `FiniteChains.ConnectedRollerModel.stepPath_base` — every vertex `A` is joined to the base
  vertex by a path of exactly `A.card` one-coordinate moves, so the model is the vertex set of
  a connected graph whose edges are the one-coordinate moves and in which `A` is at distance
  at most `A.card` from the base vertex;
* `FiniteChains.ConnectedRollerModel.stepConnected` — hence any two vertices are joined by such
  a path.

The conclusion `ker d₂ = im d₃` proved in `RequestProject/CubeRollerModel.lean` is unaffected
(it holds for every median-closed `W`); what this file adds is that under the extra hypothesis
the combinatorial data really is the data of a connected graph with one-coordinate edges.
-/

namespace FiniteChains

universe u

variable {ι : Type u} [DecidableEq ι]

/-- A single move inside `W` changing exactly one coordinate: `B` is obtained from `A` by
deleting or inserting one hyperplane, and both are vertices. -/
def OneStep (W : Set (Finset ι)) (A B : Finset ι) : Prop :=
  A ∈ W ∧ B ∈ W ∧ ∃ p : ι, (p ∈ A ∧ B = A.erase p) ∨ (p ∈ B ∧ A = B.erase p)

theorem OneStep.symm {W : Set (Finset ι)} {A B : Finset ι} (h : OneStep W A B) :
    OneStep W B A := by
  obtain ⟨hA, hB, p, hp⟩ := h
  exact ⟨hB, hA, p, hp.symm⟩

/-- A path of one-coordinate moves inside `W`, together with its length. -/
inductive StepPath (W : Set (Finset ι)) : Finset ι → Finset ι → ℕ → Prop
  | nil {A : Finset ι} (hA : A ∈ W) : StepPath W A A 0
  | cons {A B C : Finset ι} {n : ℕ} (h : OneStep W A B) (t : StepPath W B C n) :
      StepPath W A C (n + 1)

theorem StepPath.start_mem {W : Set (Finset ι)} {A B : Finset ι} {n : ℕ}
    (h : StepPath W A B n) : A ∈ W := by
  cases h with
  | nil hA => exact hA
  | cons h _ => exact h.1

theorem StepPath.append {W : Set (Finset ι)} {A B C : Finset ι} {m n : ℕ}
    (h₁ : StepPath W A B m) (h₂ : StepPath W B C n) : StepPath W A C (m + n) := by
  induction h₁ with
  | nil _ => simpa using h₂
  | cons h _ ih =>
      rename_i m' _
      have : StepPath W _ C (m' + n) := ih h₂
      simpa [Nat.succ_add] using StepPath.cons h this

theorem StepPath.reverse {W : Set (Finset ι)} {A B : Finset ι} {n : ℕ}
    (h : StepPath W A B n) : StepPath W B A n := by
  induction h with
  | nil hA => exact StepPath.nil hA
  | cons h _ ih =>
      rename_i n' t
      have := ih.append (StepPath.cons h.symm (StepPath.nil h.1))
      simpa [Nat.add_comm] using this

theorem StepPath.exists_oneStep {W : Set (Finset ι)} {A B : Finset ι} {n : ℕ}
    (h : StepPath W A B n) (hne : A ≠ B) : ∃ C : Finset ι, OneStep W A C := by
  cases h with
  | nil hA => exact absurd rfl hne
  | cons hstep _ => exact ⟨_, hstep⟩

/-- A **Roller model with descending neighbours**: besides being closed under the median, the
vertex set is required to contain, for every vertex other than the base vertex, a vertex
obtained from it by deleting one hyperplane.  This is the hypothesis that makes the model the
vertex set of a connected graph with one-coordinate edges; median-closedness alone does not
imply it (`FiniteChains.pairModel_not_stepConnected`). -/
structure ConnectedRollerModel (ι : Type u) [DecidableEq ι] extends RollerModel ι where
  /-- Every non-base vertex has a descending neighbour inside the model. -/
  desc : ∀ A ∈ toRollerModel.W, A.Nonempty → ∃ p ∈ A, A.erase p ∈ toRollerModel.W

namespace ConnectedRollerModel

variable (R : ConnectedRollerModel ι)

/-- **Every vertex is joined to the base vertex by one-coordinate moves**, and the number of
moves is exactly the number of hyperplanes separating it from the base vertex. -/
theorem stepPath_base_aux (n : ℕ) : ∀ A ∈ R.W, A.card = n → StepPath R.W A ∅ A.card := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hA hn
    rcases Finset.eq_empty_or_nonempty A with rfl | hne
    · exact StepPath.nil hA
    · obtain ⟨p, hp, hmem⟩ := R.desc A hA hne
      have hpos : 0 < A.card := Finset.card_pos.mpr hne
      have hcard : (A.erase p).card + 1 = A.card := by
        rw [Finset.card_erase_of_mem hp]
        omega
      have hlt : (A.erase p).card < n := by omega
      have hrec := ih (A.erase p).card hlt (A.erase p) hmem rfl
      have hstep : OneStep R.W A (A.erase p) := ⟨hA, hmem, p, Or.inl ⟨hp, rfl⟩⟩
      have := StepPath.cons hstep hrec
      rwa [hcard] at this

theorem stepPath_base (A : Finset ι) (hA : A ∈ R.W) : StepPath R.W A ∅ A.card :=
  R.stepPath_base_aux A.card A hA rfl

/-- **Any two vertices are joined by a path of one-coordinate moves.** -/
theorem stepConnected {A B : Finset ι} (hA : A ∈ R.W) (hB : B ∈ R.W) :
    ∃ n : ℕ, StepPath R.W A B n :=
  ⟨A.card + B.card, (R.stepPath_base A hA).append (R.stepPath_base B hB).reverse⟩

end ConnectedRollerModel

section Counterexample

variable {p q : ι}

/-- The two-element vertex set `{∅, {p, q}}`. -/
def pairSet (p q : ι) : Set (Finset ι) := {∅, {p, q}}

/-- `{∅, {p, q}}` is closed under the median (majority) operation. -/
theorem pairSet_med_mem {A B C : Finset ι} (hA : A ∈ pairSet p q) (hB : B ∈ pairSet p q)
    (hC : C ∈ pairSet p q) : medFinset A B C ∈ pairSet p q := by
  have h : ∀ {X : Finset ι}, X ∈ pairSet p q → X = ∅ ∨ X = {p, q} := by
    rintro X (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases h hA with rfl | rfl <;> rcases h hB with rfl | rfl <;> rcases h hC with rfl | rfl <;>
    simp [medFinset, pairSet]

/-- `{∅, {p, q}}` contains the base vertex. -/
theorem pairSet_base_mem : (∅ : Finset ι) ∈ pairSet p q := Or.inl rfl

/-- **Median-closedness alone does not give one-coordinate paths**: in the median-closed set
`{∅, {p, q}}` there is no path of one-coordinate moves from `{p, q}` to the base vertex `∅`.
This is why `FiniteChains.ConnectedRollerModel` records the descending hypothesis. -/
theorem pairModel_not_stepConnected (hpq : p ≠ q) (n : ℕ) :
    ¬ StepPath (pairSet p q) {p, q} ∅ n := by
  have hcard : ({p, q} : Finset ι).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hpq), Finset.card_singleton]
  have hne : ({p, q} : Finset ι) ≠ ∅ := by
    intro h
    rw [h] at hcard
    simp at hcard
  intro h
  obtain ⟨C, -, hC, r, hr⟩ := h.exists_oneStep hne
  rcases hC with rfl | rfl
  · rcases hr with ⟨hrA, hB⟩ | ⟨hrB, -⟩
    · have : (∅ : Finset ι).card + 1 = ({p, q} : Finset ι).card := by
        rw [hB, Finset.card_erase_of_mem hrA, hcard]
      simp [hcard] at this
    · simp at hrB
  · rcases hr with ⟨hrA, hB⟩ | ⟨hrB, hA⟩
    · have : ({p, q} : Finset ι).card + 1 = ({p, q} : Finset ι).card := by
        nth_rewrite 1 [hB]
        rw [Finset.card_erase_of_mem hrA, hcard]
      omega
    · have hc := congrArg Finset.card hA
      rw [Finset.card_erase_of_mem hrB, hcard] at hc
      omega

end Counterexample

end FiniteChains
