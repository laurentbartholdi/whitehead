module

public import Mathlib

@[expose] public section

/-!
# Abstract simplicial complexes, flagness, and barycentric subdivisions

Section 3.3 of the paper uses the cubical curvature criterion: a cube complex all of whose
vertex links are *flag* simplicial complexes has a CAT(0) universal cover.  Two purely
combinatorial claims enter the verification of that hypothesis for the complexes `C(L_q)`:

* the barycentric subdivision of a simplicial complex is flag
  ("It is flag: pairwise comparable faces form a chain");
* a disjoint union of flag complexes is flag (used in Step 2 of the proof of the generation
  lemma, where the link of a new vertex is a disjoint union of covers of `L_q`).

Both are proved here for abstract simplicial complexes in the usual combinatorial sense.
The barycentric subdivision is realized, as usual, as the order complex (the complex of
finite chains) of the poset of nonempty faces.
-/

namespace FiniteChains

universe u

variable {V : Type u}

/-- An abstract simplicial complex on the vertex type `V`: a downward closed family of
finite subsets of `V` containing the empty face. -/
structure ASC (V : Type u) where
  /-- The family of faces. -/
  faces : Set (Finset V)
  /-- The empty simplex is a face. -/
  empty_mem : (∅ : Finset V) ∈ faces
  /-- Faces are closed under passing to subsets. -/
  down_closed : ∀ {s t : Finset V}, s ∈ faces → t ⊆ s → t ∈ faces

namespace ASC

/-- `K` is *flag* if every finite clique spans a simplex: a finite set of vertices all of
whose at most two element subsets are faces is itself a face. -/
def IsFlag (K : ASC V) : Prop :=
  ∀ s : Finset V, (∀ t ⊆ s, t.card ≤ 2 → t ∈ K.faces) → s ∈ K.faces

/-- The order complex of a preorder: its faces are the finite chains. -/
def orderComplex (P : Type u) [Preorder P] : ASC P where
  faces := {s : Finset P | IsChain (· ≤ ·) (s : Set P)}
  empty_mem := by simp [IsChain, Set.Pairwise]
  down_closed := by
    intro s t hs hts
    exact hs.mono (by exact_mod_cast hts)

@[simp] theorem mem_orderComplex {P : Type u} [Preorder P] {s : Finset P} :
    s ∈ (orderComplex P).faces ↔ IsChain (· ≤ ·) (s : Set P) := Iff.rfl

/-- **The order complex of a preorder is flag**: a finite set of pairwise comparable
elements is a chain. -/
theorem orderComplex_isFlag (P : Type u) [Preorder P] : (orderComplex P).IsFlag := by
  classical
  intro s hs x hx y hy hxy
  have hx' : x ∈ s := by exact_mod_cast hx
  have hy' : y ∈ s := by exact_mod_cast hy
  have hsub : ({x, y} : Finset P) ⊆ s := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have hcard : ({x, y} : Finset P).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
  have hchain := hs _ hsub hcard
  exact hchain (by simp) (by simp) hxy

/-- The poset of nonempty faces of `K`, ordered by inclusion. -/
def Face (K : ASC V) : Type u := {s : Finset V // s ∈ K.faces ∧ s.Nonempty}

instance (K : ASC V) : Preorder K.Face := Subtype.preorder _

/-- The barycentric subdivision of `K`: the order complex of its poset of nonempty faces. -/
def barycentric (K : ASC V) : ASC K.Face := orderComplex K.Face

/-- **The barycentric subdivision of a simplicial complex is flag.** -/
theorem barycentric_isFlag (K : ASC V) : K.barycentric.IsFlag := orderComplex_isFlag _

/-- The full subcomplex of `K` spanned by the vertices satisfying `P`. -/
def restrict (K : ASC V) (P : V → Prop) : ASC V where
  faces := {s | s ∈ K.faces ∧ ∀ x ∈ s, P x}
  empty_mem := ⟨K.empty_mem, by simp⟩
  down_closed := fun hs hts => ⟨K.down_closed hs.1 hts, fun _ hx => hs.2 _ (hts hx)⟩

theorem restrict_faces_subset (K : ASC V) (P : V → Prop) :
    (K.restrict P).faces ⊆ K.faces := fun _ hs => hs.1

/-- **A disjoint union of flag complexes is flag.**  Here the decomposition of `K` into
components is recorded by a map `p : V → ι` such that every face of `K` is contained in a
single fibre of `p`; the components are the full subcomplexes spanned by the fibres. -/
theorem isFlag_of_fibres {ι : Type u} (K : ASC V) (p : V → ι)
    (hsep : ∀ s ∈ K.faces, ∀ x ∈ s, ∀ y ∈ s, p x = p y)
    (hflag : ∀ i, (K.restrict (fun x => p x = i)).IsFlag) : K.IsFlag := by
  classical
  intro s hs
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact K.empty_mem
  -- all vertices of `s` lie in the fibre of `x₀`
  have hfib : ∀ x ∈ s, p x = p x₀ := by
    intro x hx
    by_cases hxx : x = x₀
    · rw [hxx]
    · have hsub : ({x, x₀} : Finset V) ⊆ s := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      have hcard : ({x, x₀} : Finset V).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
      exact hsep _ (hs _ hsub hcard) x (by simp) x₀ (by simp)
  have := hflag (p x₀) s (by
    intro t hts hcard
    exact ⟨hs t hts hcard, fun x hx => hfib x (hts hx)⟩)
  exact this.1

end ASC

end FiniteChains
