module

public import Mathlib

@[expose] public section

/-!
# Collapsing the top cells: the spine argument of Lemma 3.2 (ii)

Lemma 3.2 (ii) of the paper asserts that the truncated cube complex `M_q` collapses onto a
finite two-dimensional spine, and proves it as follows: every square meets at most two
three-cubes; the adjacency graph of the three-cells across their two-faces is connected;
one chooses a spanning tree rooted at a cell meeting the cut surface, collapses the root
across a cut face, and then each further cell across the face it formerly shared with its
parent — that face is free once the parent has been removed.

This file proves the combinatorial content of that argument, for an arbitrary finite family
of top cells `T` whose codimension one faces `F` satisfy the only property used: *a face is
contained in at most two top cells*.  An elementary collapse removes a top cell together
with a face which, at that moment, is contained in no other remaining top cell (`IsFree`),
and `IsCollapse` records a sequence of such moves removing a whole set of top cells.

The main results are:

* `FiniteChains.Collapse.exists_isCollapse`: a set of top cells can be collapsed away
  completely as soon as every nonempty subset closed under adjacency contains a cell with a
  free face — the invariant that the spanning-tree argument maintains;
* `FiniteChains.Collapse.exists_isCollapse_of_connected`: in particular, if the adjacency
  graph is connected and *one* cell has a free face (for `M_q`: a cell meeting the cut
  surface), then all top cells disappear.
-/

namespace FiniteChains
namespace Collapse

variable {T F : Type*} [DecidableEq T]

variable (inc : F → Finset T)

/-- Two distinct top cells are adjacent if they share a codimension one face. -/
def Adj (t t' : T) : Prop := t ≠ t' ∧ ∃ f, t ∈ inc f ∧ t' ∈ inc f

/-- The face `f` is *free* for the set `S` of remaining top cells if `t` is the only
remaining top cell containing it. -/
def IsFree (S : Finset T) (f : F) (t : T) : Prop := inc f ∩ S = {t}

/-- `t` admits an elementary collapse in `S`: some face of `t` is free for `S`. -/
def HasFreeFace (S : Finset T) (t : T) : Prop := ∃ f, IsFree inc S f t

/-- A sequence of elementary collapses removing exactly the top cells of `S`. -/
def IsCollapse : List T → Finset T → Prop
  | [], S => S = ∅
  | t :: l, S => t ∈ S ∧ HasFreeFace inc S t ∧ IsCollapse l (S.erase t)

/-- The invariant maintained by the spanning-tree argument: every nonempty subset of the
remaining cells which is closed under adjacency contains a cell with a free face. -/
def Collapsible (S : Finset T) : Prop :=
  ∀ C : Finset T, C ⊆ S → C.Nonempty → (∀ c ∈ C, ∀ t ∈ S, Adj inc c t → t ∈ C) →
    ∃ c ∈ C, HasFreeFace inc S c

/-- Connectivity of the adjacency graph inside `S`. -/
def Connected (S : Finset T) : Prop :=
  ∀ t ∈ S, ∀ t' ∈ S, Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ Adj inc a b) t t'

variable {inc}

/-- A nonempty collapsible set has a cell with a free face. -/
theorem exists_hasFreeFace {S : Finset T} (hS : Collapsible inc S) (hne : S.Nonempty) :
    ∃ t ∈ S, HasFreeFace inc S t :=
  hS S (Finset.Subset.refl S) hne fun _ _ _ ht _ => ht

/-- **Collapsibility is preserved by an elementary collapse.**  This is the step "the face
formerly shared with the parent is free once the parent has been removed": a subset that
becomes closed only after the removal of `t` contains a neighbour of `t`, and the shared
face is free for the smaller set. -/
theorem collapsible_erase (hcard : ∀ f, (inc f).card ≤ 2) {S : Finset T}
    (hS : Collapsible inc S) (t : T) : Collapsible inc (S.erase t) := by
  intro C hCS hne hclosed
  by_cases hadj : ∃ c ∈ C, Adj inc c t
  · -- the shared face becomes free
    obtain ⟨c, hcC, hne', f, htf, hcf⟩ := hadj
    refine ⟨c, hcC, f, ?_⟩
    have hsub : ({t, c} : Finset T) ⊆ inc f := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    have hcard2 : ({t, c} : Finset T).card = 2 := by
      rw [Finset.card_pair]
      exact fun hh => hne' hh.symm
    have hfeq : inc f = {t, c} :=
      (Finset.eq_of_subset_of_card_le hsub (by rw [hcard2]; exact hcard f)).symm
    have hcS : c ∈ S.erase t := hCS hcC
    ext z
    simp only [hfeq, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_erase]
    constructor
    · rintro ⟨hz | hz, hzS⟩
      · exact absurd hz hzS.1
      · exact hz
    · rintro rfl
      exact ⟨Or.inr rfl, Finset.mem_erase.1 hcS⟩
  · -- `C` was already closed in `S`, so the invariant applies directly
    push_neg at hadj
    have hCS' : C ⊆ S := hCS.trans (Finset.erase_subset _ _)
    have hclosed' : ∀ c ∈ C, ∀ u ∈ S, Adj inc c u → u ∈ C := by
      intro c hc u huS hcu
      have hut : u ≠ t := by
        rintro rfl
        exact hadj c hc hcu
      exact hclosed c hc u (Finset.mem_erase.2 ⟨hut, huS⟩) hcu
    obtain ⟨c, hcC, f, hf⟩ := hS C hCS' hne hclosed'
    refine ⟨c, hcC, f, ?_⟩
    have hct : c ≠ t := (Finset.mem_erase.1 (hCS hcC)).1
    ext z
    constructor
    · intro hz
      simp only [Finset.mem_inter, Finset.mem_erase] at hz
      have : z ∈ inc f ∩ S := Finset.mem_inter.2 ⟨hz.1, hz.2.2⟩
      rwa [hf] at this
    · intro hz
      simp only [Finset.mem_singleton] at hz
      subst hz
      have hzf : z ∈ inc f ∩ S := by rw [hf]; simp
      simp only [Finset.mem_inter] at hzf
      exact Finset.mem_inter.2 ⟨hzf.1, Finset.mem_erase.2 ⟨hct, hzf.2⟩⟩

/-- **All top cells of a collapsible set can be collapsed away.** -/
theorem exists_isCollapse (hcard : ∀ f, (inc f).card ≤ 2) :
    ∀ (n : ℕ) (S : Finset T), S.card = n → Collapsible inc S → ∃ l : List T, IsCollapse inc l S
  | 0, S, hn, _ => ⟨[], Finset.card_eq_zero.1 hn⟩
  | n + 1, S, hn, hS => by
      have hne : S.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨t, htS, hfree⟩ := exists_hasFreeFace hS hne
      have hcard' : (S.erase t).card = n := by
        rw [Finset.card_erase_of_mem htS, hn]
        omega
      obtain ⟨l, hl⟩ :=
        exists_isCollapse hcard n (S.erase t) hcard' (collapsible_erase hcard hS t)
      exact ⟨t :: l, htS, hfree, hl⟩

/-- A connected set of top cells one of which has a free face is collapsible. -/
theorem collapsible_of_connected {S : Finset T} (hconn : Connected inc S)
    {t₀ : T} (ht₀ : t₀ ∈ S) (hfree : HasFreeFace inc S t₀) : Collapsible inc S := by
  intro C hCS hne hclosed
  obtain ⟨c, hcC⟩ := hne
  have hcS : c ∈ S := hCS hcC
  have key : ∀ x, Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ Adj inc a b) c x →
      x ∈ C := by
    intro x hx
    induction hx with
    | refl => exact hcC
    | tail _ hstep ih => exact hclosed _ ih _ hstep.2.1 hstep.2.2
  exact ⟨t₀, key t₀ (hconn c hcS t₀ ht₀), hfree⟩

/-- **The collapse of Lemma 3.2 (ii).**  If every codimension one face lies in at most two
top cells, the adjacency graph of the top cells is connected, and one top cell has a free
face, then all top cells can be removed by elementary collapses. -/
theorem exists_isCollapse_of_connected (hcard : ∀ f, (inc f).card ≤ 2) {S : Finset T}
    (hconn : Connected inc S) {t₀ : T} (ht₀ : t₀ ∈ S) (hfree : HasFreeFace inc S t₀) :
    ∃ l : List T, IsCollapse inc l S :=
  exists_isCollapse hcard S.card S rfl (collapsible_of_connected hconn ht₀ hfree)

/-! ### A nonempty instance -/

/-- Two top cells glued along one face, with a free face on each side: the smallest
instance of the collapse theorem. -/
def exInc : Fin 3 → Finset (Fin 2)
  | 0 => {0}
  | 1 => {0, 1}
  | 2 => {1}

theorem exInc_card : ∀ f : Fin 3, (exInc f).card ≤ 2 := by decide

theorem exInc_collapse : IsCollapse exInc [0, 1] {0, 1} := by
  refine ⟨by decide, ⟨0, ?_⟩, by decide, ⟨2, ?_⟩, ?_⟩
  · show exInc 0 ∩ {0, 1} = {0}
    decide
  · show exInc 2 ∩ ({0, 1} : Finset (Fin 2)).erase 0 = {1}
    decide
  · show (({0, 1} : Finset (Fin 2)).erase 0).erase 1 = ∅
    decide

end Collapse
end FiniteChains
