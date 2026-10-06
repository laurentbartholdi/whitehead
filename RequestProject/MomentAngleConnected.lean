import RequestProject.TruncatedCube

/-!
# Connectivity of the adjacency graph of the three-cubes of `C(L)`

The collapse argument of Lemma 3.2 (ii) needs the statement quoted in the paper as
"the adjacency graph of three-cells across two-faces is connected: triangle adjacency joins
the cubes at each sign vertex, and adjacent sign vertices share three-cubes".

This file proves it for the cube complex `C(L)` of `RequestProject/MomentAngle.lean`.  A
*move* passes from the cube with free set `τ ∪ {c}` to the cube with free set `τ ∪ {c'}`,
the two agreeing at all other coordinates; the two cubes then share the square with free
set `τ` (`Move.shares_square`), so a chain of moves is a path in the adjacency graph.

The hypotheses are exactly the two combinatorial properties of a triangulated surface used
in the paper: the dual graph of `L` (triangles joined along shared edges) is connected, and
every vertex lies in a triangle.  The proof is the one sketched there: signs are changed
only at the vertex that a move frees, and a move may always set that sign to `+1`, so every
cube can be driven to the all-`+1` cube over a fixed triangle.
-/

namespace FiniteChains

open Finset

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- A triangle of `L`: a face with three vertices. -/
def IsTri (L : ASC V) (σ : Finset V) : Prop := σ ∈ L.faces ∧ σ.card = 3

/-- Adjacency of triangles in the dual graph of `L`: they share an edge. -/
def TriAdj (L : ASC V) (σ σ' : Finset V) : Prop :=
  IsTri L σ ∧ IsTri L σ' ∧ (σ ∩ σ').card = 2

/-- The vertices at which a cube has the sign `-1`. -/
def negSet (f : Cube V) : Finset V := univ.filter fun v => f v = CubeCoord.neg

omit [DecidableEq V] [LinearOrder V] in
@[simp] theorem mem_negSet {f : Cube V} {v : V} : v ∈ negSet f ↔ f v = CubeCoord.neg := by
  simp [negSet]

omit [LinearOrder V] in
theorem eq_posCube_of_negSet_empty {f : Cube V} (h : negSet f = ∅) :
    f = posCube (freeSet f) := by
  funext v
  by_cases hv : f v = CubeCoord.free
  · simp [posCube, hv]
  · have hvn : f v ≠ CubeCoord.neg := by
      intro hn
      have : v ∈ negSet f := by simpa using hn
      simp [h] at this
    have hvp : f v = CubeCoord.pos := by
      cases hfv : f v with
      | free => exact absurd hfv hv
      | pos => rfl
      | neg => exact absurd hfv hvn
    have : v ∉ freeSet f := by simpa using hv
    simp [posCube, this, hvp]

/-- An elementary move of the adjacency graph: free the coordinate `c'` and fix the
coordinate `c`, leaving the other coordinates untouched.  Both cubes are required to lie in
`C(L)`. -/
def Move (L : ASC V) (f g : Cube V) : Prop :=
  ∃ c c' : V, c ≠ c' ∧ f c = CubeCoord.free ∧ f c' ≠ CubeCoord.free ∧
    g c ≠ CubeCoord.free ∧ g c' = CubeCoord.free ∧
    (∀ v, v ≠ c → v ≠ c' → f v = g v) ∧ freeSet f ∈ L.faces ∧ freeSet g ∈ L.faces

omit [LinearOrder V] in
omit [DecidableEq V] in
theorem Move.symm {L : ASC V} {f g : Cube V} (h : Move L f g) : Move L g f := by
  obtain ⟨c, c', hcc, hfc, hfc', hgc, hgc', hagree, hfL, hgL⟩ := h
  exact ⟨c', c, hcc.symm, hgc', hgc, hfc', hfc, fun v hv hv' => (hagree v hv' hv).symm, hgL, hfL⟩

omit [LinearOrder V] in
/-- Two cubes joined by a move share a codimension one face: the cube obtained by fixing
the coordinate `c` as in `g` and the coordinate `c'` as in `f`. -/
theorem Move.shares_square {L : ASC V} {f g : Cube V} (h : Move L f g) :
    ∃ s : Cube V, (∃ j, s j ≠ CubeCoord.free ∧ f = Function.update s j CubeCoord.free) ∧
      (∃ j, s j ≠ CubeCoord.free ∧ g = Function.update s j CubeCoord.free) := by
  obtain ⟨c, c', hcc, hfc, hfc', hgc, hgc', hagree, -, -⟩ := h
  refine ⟨fun v => if v = c then g c else if v = c' then f c' else f v, ⟨c, ?_, ?_⟩,
    ⟨c', ?_, ?_⟩⟩
  · simpa using hgc
  · funext v
    by_cases hv : v = c
    · subst hv; simp [hfc]
    · by_cases hv' : v = c'
      · subst hv'; simp [hv]
      · simp [hv, hv']
  · simp [hcc.symm, hfc']
  · funext v
    by_cases hv : v = c'
    · subst hv; simp [hgc']
    · by_cases hvc : v = c
      · subst hvc; simp [hv]
      · simp [hv, hvc, hagree v hvc hv]

/-- The result of a single move which frees `c'` and gives the sign `+1` to `c`. -/
def moveTo (f : Cube V) (c c' : V) : Cube V := fun v =>
  if v = c then CubeCoord.pos else if v = c' then CubeCoord.free else f v

omit [LinearOrder V] in
theorem freeSet_moveTo {f : Cube V} {c c' : V} (hcc : c ≠ c') (hfc : f c = CubeCoord.free) :
    freeSet (moveTo f c c') = insert c' ((freeSet f).erase c) := by
  ext v
  by_cases hv : v = c
  · subst hv
    simp [moveTo, hcc]
  · by_cases hv' : v = c'
    · subst hv'
      simp [moveTo, hv]
    · simp [moveTo, hv, hv']

omit [LinearOrder V] in
theorem negSet_moveTo_subset (f : Cube V) (c c' : V) : negSet (moveTo f c c') ⊆ negSet f := by
  intro v hv
  simp only [mem_negSet, moveTo] at hv ⊢
  by_cases hvc : v = c
  · simp [hvc] at hv
  · by_cases hvc' : v = c'
    · have hne : c' ≠ c := by
        rintro rfl
        exact hvc hvc'
      simp [hvc', hne] at hv
    · simpa [hvc, hvc'] using hv

omit [LinearOrder V] in
/-- An elementary move along an edge of the dual graph of `L`. -/
theorem move_moveTo {L : ASC V} {f : Cube V} {c c' : V} (hcc : c ≠ c')
    (hfc : f c = CubeCoord.free) (hfc' : f c' ≠ CubeCoord.free) (hfL : freeSet f ∈ L.faces)
    (hgL : freeSet (moveTo f c c') ∈ L.faces) : Move L f (moveTo f c c') := by
  refine ⟨c, c', hcc, hfc, hfc', ?_, ?_, ?_, hfL, hgL⟩
  · simp [moveTo]
  · simp [moveTo, hcc.symm]
  · intro v hv hv'
    simp [moveTo, hv, hv']

omit [Fintype V] [LinearOrder V] in
/-- Two triangles sharing an edge differ in exactly one vertex each. -/
theorem exists_pair_of_triAdj {L : ASC V} {σ σ' : Finset V} (h : TriAdj L σ σ') :
    ∃ c c', c ≠ c' ∧ c ∈ σ ∧ c ∉ σ' ∧ c' ∈ σ' ∧ c' ∉ σ ∧ σ' = insert c' (σ.erase c) := by
  obtain ⟨⟨-, hcard⟩, ⟨-, hcard'⟩, hint⟩ := h
  have hdiff : (σ \ σ').card = 1 := by
    have := Finset.card_sdiff_add_card_inter σ σ'
    omega
  have hdiff' : (σ' \ σ).card = 1 := by
    have := Finset.card_sdiff_add_card_inter σ' σ
    rw [Finset.inter_comm] at this
    omega
  obtain ⟨c, hc⟩ := Finset.card_eq_one.1 hdiff
  obtain ⟨c', hc'⟩ := Finset.card_eq_one.1 hdiff'
  have hcmem : c ∈ σ \ σ' := by rw [hc]; simp
  have hc'mem : c' ∈ σ' \ σ := by rw [hc']; simp
  simp only [Finset.mem_sdiff] at hcmem hc'mem
  refine ⟨c, c', ?_, hcmem.1, hcmem.2, hc'mem.1, hc'mem.2, ?_⟩
  · rintro rfl
    exact hcmem.2 hc'mem.1
  · apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_erase]
      by_cases hzc' : z = c'
      · exact Or.inl hzc'
      · refine Or.inr ⟨?_, ?_⟩
        · rintro rfl
          exact hcmem.2 hz
        · by_contra hzσ
          have : z ∈ σ' \ σ := Finset.mem_sdiff.2 ⟨hz, hzσ⟩
          rw [hc'] at this
          exact hzc' (Finset.mem_singleton.1 this)
    · have h1 : (insert c' (σ.erase c)).card ≤ (σ.erase c).card + 1 := Finset.card_insert_le _ _
      have h2 : (σ.erase c).card = σ.card - 1 := Finset.card_erase_of_mem hcmem.1
      omega

omit [LinearOrder V] in
/-- **Moving along a path in the dual graph of `L`.**  A cube over the triangle `σ` can be
driven to a cube over any triangle joined to `σ` in the dual graph, and the moves never
create new `-1` signs. -/
theorem exists_move_path {L : ASC V} {σ σ' : Finset V}
    (hpath : Relation.ReflTransGen (TriAdj L) σ σ') :
    ∀ f : Cube V, freeSet f = σ → ∃ g : Cube V, freeSet g = σ' ∧ negSet g ⊆ negSet f ∧
      Relation.ReflTransGen (Move L) f g := by
  induction hpath with
  | refl => exact fun f hf => ⟨f, hf, Finset.Subset.refl _, Relation.ReflTransGen.refl⟩
  | @tail τ τ' hchain hstep ih =>
      intro f hf
      obtain ⟨g, hgfree, hgneg, hgpath⟩ := ih f hf
      obtain ⟨c, c', hcc, hcτ, hcτ', hc'τ', hc'τ, hτ'⟩ := exists_pair_of_triAdj hstep
      have hgc : g c = CubeCoord.free := by
        have : c ∈ freeSet g := by rw [hgfree]; exact hcτ
        simpa using this
      have hgc' : g c' ≠ CubeCoord.free := by
        intro hcon
        have : c' ∈ freeSet g := by simpa using hcon
        rw [hgfree] at this
        exact hc'τ this
      have hfreeNew : freeSet (moveTo g c c') = τ' := by
        rw [freeSet_moveTo hcc hgc, hgfree, hτ']
      refine ⟨moveTo g c c', hfreeNew, (negSet_moveTo_subset g c c').trans hgneg, ?_⟩
      refine hgpath.tail (move_moveTo hcc hgc hgc' ?_ ?_)
      · rw [hgfree]; exact hstep.1.1
      · rw [hfreeNew]; exact hstep.2.1.1

omit [LinearOrder V] in
/-- Every cube of `C(L)` over a triangle can be driven to the all-`+1` cube over a fixed
triangle. -/
theorem reflTransGen_move_posCube {L : ASC V} (hdual : ∀ σ σ', IsTri L σ → IsTri L σ' →
      Relation.ReflTransGen (TriAdj L) σ σ')
    (hcover : ∀ v : V, ∃ σ, IsTri L σ ∧ v ∈ σ) {σ₀ : Finset V} (hσ₀ : IsTri L σ₀) :
    ∀ (n : ℕ) (f : Cube V), IsTri L (freeSet f) → (negSet f).card ≤ n →
      Relation.ReflTransGen (Move L) f (posCube σ₀)
  | 0, f, hf, hn => by
      have hempty : negSet f = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hn)
      obtain ⟨g, hgfree, hgneg, hgpath⟩ :=
        exists_move_path (hdual _ _ hf hσ₀) f rfl
      have hgempty : negSet g = ∅ := Finset.subset_empty.1 (hempty ▸ hgneg)
      have : g = posCube σ₀ := by
        rw [eq_posCube_of_negSet_empty hgempty, hgfree]
      rwa [this] at hgpath
  | n + 1, f, hf, hn => by
      rcases (negSet f).eq_empty_or_nonempty with hempty | ⟨v, hv⟩
      · exact reflTransGen_move_posCube hdual hcover hσ₀ 0 f hf (by simp [hempty])
      · obtain ⟨τ, hτ, hvτ⟩ := hcover v
        obtain ⟨g, hgfree, hgneg, hgpath⟩ := exists_move_path (hdual _ _ hf hτ) f rfl
        have hvg : v ∉ negSet g := by
          intro hcon
          have hvfree : g v = CubeCoord.free := by
            have : v ∈ freeSet g := by rw [hgfree]; exact hvτ
            simpa using this
          rw [mem_negSet] at hcon
          rw [hvfree] at hcon
          exact CubeCoord.noConfusion hcon
        have hstrict : (negSet g).card < (negSet f).card :=
          Finset.card_lt_card ⟨hgneg, fun hcon => hvg (hcon hv)⟩
        have hgtri : IsTri L (freeSet g) := by rw [hgfree]; exact hτ
        have : (negSet g).card ≤ n := by omega
        exact hgpath.trans (reflTransGen_move_posCube hdual hcover hσ₀ n g hgtri this)

omit [LinearOrder V] in
/-- **The adjacency graph of the three-cubes of `C(L)` is connected.**  The hypotheses are
the two combinatorial properties of a triangulated closed surface that the paper uses: the
dual graph of `L` is connected, and every vertex of `L` lies in a triangle. -/
theorem reflTransGen_move {L : ASC V} (hdual : ∀ σ σ', IsTri L σ → IsTri L σ' →
      Relation.ReflTransGen (TriAdj L) σ σ')
    (hcover : ∀ v : V, ∃ σ, IsTri L σ ∧ v ∈ σ) {f g : Cube V}
    (hf : IsTri L (freeSet f)) (hg : IsTri L (freeSet g)) :
    Relation.ReflTransGen (Move L) f g := by
  have hfp := reflTransGen_move_posCube hdual hcover hf (negSet f).card f hf le_rfl
  have hgp := reflTransGen_move_posCube hdual hcover hf (negSet g).card g hg le_rfl
  have hgp_rev : Relation.ReflTransGen (Move L) (posCube (freeSet f)) g := by
    exact Relation.ReflTransGen.mono (fun _ _ (step : Move L _ _) => step.symm) _ _
      (Relation.ReflTransGen.swap _ _ hgp)
  exact hfp.trans hgp_rev

end FiniteChains
