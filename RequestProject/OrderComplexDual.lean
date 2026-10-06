module

public import RequestProject.OrderComplexSurface
public import RequestProject.MomentAngleConnected

@[expose] public section

/-!
# The dual graph of the order complex of a two-dimensional cell poset

`RequestProject/OrderComplexSurface.lean` verifies the *local* closed surface conditions for the
order complex (barycentric subdivision) of a two-dimensional cell poset.  The collapse of
Lemma 3.2 (ii) (`FiniteChains.exists_spine_collapse_of_surface`) needs one more input, a *global*
one: the dual graph of the triangulation — triangles joined when they share an edge — has to be
connected.

The triangles of the order complex are the flags `v < e < f` (a vertex, an edge through it and a
face through that edge), and two flags which differ in exactly one entry share an edge of the
subdivision.  Connectedness of the dual graph therefore follows from two conditions on the cell
poset itself:

* `FiniteChains.ASC.FaceEdges` — two distinct vertices of a face are joined by an edge of that
  face (true for a face with three vertices, which is the case for the triangulated surfaces used
  here); this makes the flags of a *fixed* face connected;
* `FiniteChains.ASC.FacesConnected` — any two faces are joined by a chain of faces in which
  consecutive ones share an edge.

`FiniteChains.ASC.SurfaceRank.dual_connected` combines them.
-/

namespace FiniteChains

namespace ASC

open Relation

variable {P : Type} [PartialOrder P] [Fintype P] [DecidableEq P]

/-! ### Flags -/

omit [Fintype P] [DecidableEq P] in
/-- The ranks of a two-step chain in a two-dimensional cell poset are `0, 1, 2`. -/
theorem SurfaceRank.rk_flag (S : SurfaceRank P) {x y z : P} (hxy : x < y) (hyz : y < z) :
    S.rk x = 0 ∧ S.rk y = 1 ∧ S.rk z = 2 := by
  have h1 := S.rk_lt_of_lt hxy
  have h2 := S.rk_lt_of_lt hyz
  have h3 := S.rk_le_two z
  omega

omit [Fintype P] in
/-- A flag spans a triangle of the order complex. -/
theorem isTri_of_flag {v e f : P} (hve : v < e) (hef : e < f) :
    IsTri (orderComplex P) ({v, e, f} : Finset P) := by
  refine ⟨?_, ?_⟩
  · rw [mem_orderComplex]
    have : IsChain (· ≤ ·) ({v, e, f} : Set P) :=
      isChain_triple (Or.inl hve.le) (Or.inl (hve.trans hef).le) (Or.inl hef.le)
    simpa [Finset.coe_insert] using this
  · have h1 : v ≠ e := hve.ne
    have h2 : v ≠ f := (hve.trans hef).ne
    have h3 : e ≠ f := hef.ne
    rw [Finset.card_insert_of_notMem (by simp [h1, h2]),
      Finset.card_insert_of_notMem (by simp [h3])]
    simp

omit [Fintype P] in
/-- **Every triangle of the order complex is a flag.** -/
theorem orderComplex_exists_flag_of_isTri {σ : Finset P}
    (h : IsTri (orderComplex P) σ) :
    ∃ v e f : P, v < e ∧ e < f ∧ σ = ({v, e, f} : Finset P) := by
  obtain ⟨hface, hcard⟩ := h
  have hchain : IsChain (· ≤ ·) (σ : Set P) := (mem_orderComplex).1 hface
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hcard
  have hmem : ∀ x ∈ ({a, b, c} : Finset P), x ∈ (({a, b, c} : Finset P) : Set P) := by
    intro x hx; exact_mod_cast hx
  have cmp : ∀ x ∈ ({a, b, c} : Finset P), ∀ y ∈ ({a, b, c} : Finset P), x ≠ y →
      x < y ∨ y < x := by
    intro x hx y hy hxy
    rcases hchain (hmem x hx) (hmem y hy) hxy with h | h
    · exact Or.inl (lt_of_le_of_ne h hxy)
    · exact Or.inr (lt_of_le_of_ne h (Ne.symm hxy))
  have ha : a ∈ ({a, b, c} : Finset P) := by simp
  have hb : b ∈ ({a, b, c} : Finset P) := by simp
  have hc : c ∈ ({a, b, c} : Finset P) := by simp
  have perm : ∀ x y z : P, ({a, b, c} : Finset P) = {x, y, z} →
      x < y → y < z → ∃ v e f : P, v < e ∧ e < f ∧ ({a, b, c} : Finset P) = {v, e, f} :=
    fun x y z hxyz h1 h2 => ⟨x, y, z, h1, h2, hxyz⟩
  rcases cmp a ha b hb hab with h1 | h1 <;> rcases cmp b hb c hc hbc with h2 | h2 <;>
    rcases cmp a ha c hc hac with h3 | h3
  · exact perm a b c rfl h1 h2
  · exact absurd (h1.trans h2) (asymm h3)
  · exact perm a c b (by ext x; simp; tauto) h3 h2
  · exact perm c a b (by ext x; simp; tauto) h3 h1
  · exact perm b a c (by ext x; simp; tauto) h1 h3
  · exact perm b c a (by ext x; simp; tauto) h2 h3
  · exact absurd (h2.trans h1) (asymm h3)
  · exact perm c b a (by ext x; simp; tauto) h2 h1

/-! ### Adjacent flags -/

omit [PartialOrder P] [Fintype P] in
/-- Two triples which agree outside one entry meet in a pair. -/
theorem card_inter_insert {x y z z' : P} (hxy : x ≠ y) (hz : z ∉ ({x, y} : Finset P))
    (hz' : z' ∉ ({x, y} : Finset P)) (hne : z ≠ z') :
    ((insert z ({x, y} : Finset P)) ∩ (insert z' ({x, y} : Finset P))).card = 2 := by
  have hset : (insert z ({x, y} : Finset P)) ∩ (insert z' ({x, y} : Finset P))
      = ({x, y} : Finset P) := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at *
    constructor
    · rintro ⟨hw1, hw2⟩
      rcases hw1 with rfl | hw1
      · rcases hw2 with rfl | hw2
        · exact absurd rfl hne
        · exact hw2
      · exact hw1
    · intro hw
      exact ⟨Or.inr hw, Or.inr hw⟩
  rw [hset, Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]

omit [Fintype P] in
/-- Two flags over the same edge and face, with different vertices, are adjacent. -/
theorem triAdj_vtx {v v' e f : P} (hve : v < e) (hef : e < f) (hv'e : v' < e) (hvv' : v ≠ v') :
    TriAdj (orderComplex P) ({v, e, f} : Finset P) ({v', e, f} : Finset P) := by
  refine ⟨isTri_of_flag hve hef, isTri_of_flag hv'e hef, ?_⟩
  have h1 : ({v, e, f} : Finset P) = insert v ({e, f} : Finset P) := rfl
  have h2 : ({v', e, f} : Finset P) = insert v' ({e, f} : Finset P) := rfl
  rw [h1, h2]
  refine card_inter_insert hef.ne ?_ ?_ hvv'
  · simp [hve.ne, (hve.trans hef).ne]
  · simp [hv'e.ne, (hv'e.trans hef).ne]

omit [Fintype P] in
/-- Two flags over the same vertex and face, with different edges, are adjacent. -/
theorem triAdj_edge {v e e' f : P} (hve : v < e) (hef : e < f) (hve' : v < e') (he'f : e' < f)
    (hee' : e ≠ e') :
    TriAdj (orderComplex P) ({v, e, f} : Finset P) ({v, e', f} : Finset P) := by
  refine ⟨isTri_of_flag hve hef, isTri_of_flag hve' he'f, ?_⟩
  have h1 : ({v, e, f} : Finset P) = insert e ({v, f} : Finset P) := Finset.insert_comm _ _ _
  have h2 : ({v, e', f} : Finset P) = insert e' ({v, f} : Finset P) := Finset.insert_comm _ _ _
  rw [h1, h2]
  refine card_inter_insert (hve.trans hef).ne ?_ ?_ hee'
  · simp [hve.ne', hef.ne]
  · simp [hve'.ne', he'f.ne]

omit [Fintype P] in
/-- Two flags over the same vertex and edge, with different faces, are adjacent. -/
theorem triAdj_face {v e f f' : P} (hve : v < e) (hef : e < f) (hef' : e < f') (hff' : f ≠ f') :
    TriAdj (orderComplex P) ({v, e, f} : Finset P) ({v, e, f'} : Finset P) := by
  refine ⟨isTri_of_flag hve hef, isTri_of_flag hve hef', ?_⟩
  have h1 : ({v, e, f} : Finset P) = insert f ({v, e} : Finset P) := by
    ext x; simp; tauto
  have h2 : ({v, e, f'} : Finset P) = insert f' ({v, e} : Finset P) := by
    ext x; simp; tauto
  rw [h1, h2]
  refine card_inter_insert hve.ne ?_ ?_ hff'
  · simp [hef.ne', (hve.trans hef).ne']
  · simp [hef'.ne', (hve.trans hef').ne']

/-! ### The two global conditions -/

/-- Two faces are adjacent when they share an edge. -/
def FaceAdj (S : SurfaceRank P) (f f' : P) : Prop := ∃ e : P, S.rk e = 1 ∧ e < f ∧ e < f'

/-- **The faces of the cell structure are connected through shared edges.** -/
def FacesConnected (S : SurfaceRank P) : Prop :=
  ∀ f f' : P, S.rk f = 2 → S.rk f' = 2 → ReflTransGen (FaceAdj S) f f'

/-- **Two distinct vertices of a face are joined by an edge of that face.**  This holds for a
face with three vertices; it is what makes the flags of a fixed face connected. -/
def FaceEdges (S : SurfaceRank P) : Prop :=
  ∀ v v' f : P, S.rk v = 0 → S.rk v' = 0 → S.rk f = 2 → v < f → v' < f → v ≠ v' →
    ∃ e : P, v < e ∧ v' < e ∧ e < f

namespace SurfaceRank

variable (S : SurfaceRank P)

omit [Fintype P] [DecidableEq P] in
/-- A face of rank two carries a flag. -/
theorem exists_flag_of_rk_two {f : P} (hf : S.rk f = 2) :
    ∃ v e : P, S.rk v = 0 ∧ v < e ∧ e < f := by
  obtain ⟨v, hv, hvf⟩ := S.exists_vertex f hf
  obtain ⟨e, -, -, ⟨hve, hef⟩, -, -⟩ := S.two_edges v f hv hf hvf
  exact ⟨v, e, hv, hve, hef⟩

omit [Fintype P] in
/-- **The flags of a fixed face are connected in the dual graph.** -/
theorem conn_in_face (hfe : FaceEdges S) {f v e v' e' : P} (hf : S.rk f = 2)
    (hv : S.rk v = 0) (hve : v < e) (hef : e < f)
    (hv' : S.rk v' = 0) (hv'e' : v' < e') (he'f : e' < f) :
    ReflTransGen (TriAdj (orderComplex P)) ({v, e, f} : Finset P) ({v', e', f} : Finset P) := by
  by_cases hvv' : v = v'
  · subst hvv'
    by_cases hee' : e = e'
    · subst hee'; exact ReflTransGen.refl
    · exact ReflTransGen.single (triAdj_edge hve hef hv'e' he'f hee')
  · obtain ⟨e'', hve'', hv'e'', he''f⟩ :=
      hfe v v' f hv hv' hf (hve.trans hef) (hv'e'.trans he'f) hvv'
    have s1 : ReflTransGen (TriAdj (orderComplex P)) ({v, e, f} : Finset P)
        ({v, e'', f} : Finset P) := by
      by_cases h : e = e''
      · subst h; exact ReflTransGen.refl
      · exact ReflTransGen.single (triAdj_edge hve hef hve'' he''f h)
    have s2 : ReflTransGen (TriAdj (orderComplex P)) ({v, e'', f} : Finset P)
        ({v', e'', f} : Finset P) :=
      ReflTransGen.single (triAdj_vtx hve'' he''f hv'e'' hvv')
    have s3 : ReflTransGen (TriAdj (orderComplex P)) ({v', e'', f} : Finset P)
        ({v', e', f} : Finset P) := by
      by_cases h : e'' = e'
      · subst h; exact ReflTransGen.refl
      · exact ReflTransGen.single (triAdj_edge hv'e'' he''f hv'e' he'f h)
    exact (s1.trans s2).trans s3

omit [Fintype P] in
/-- Crossing a shared edge: any flag of `f` is connected to any flag of an adjacent face `f'`. -/
theorem conn_face_step (hfe : FaceEdges S) {f f' v e v' e' : P} (hadj : FaceAdj S f f')
    (hv : S.rk v = 0) (hve : v < e) (hef : e < f)
    (hv' : S.rk v' = 0) (hv'e' : v' < e') (he'f' : e' < f') :
    ReflTransGen (TriAdj (orderComplex P)) ({v, e, f} : Finset P) ({v', e', f'} : Finset P) := by
  obtain ⟨d, hd, hdf, hdf'⟩ := hadj
  have hf : S.rk f = 2 := by have := S.rk_lt_of_lt hdf; have := S.rk_le_two f; omega
  have hf' : S.rk f' = 2 := by have := S.rk_lt_of_lt hdf'; have := S.rk_le_two f'; omega
  obtain ⟨w, -, -, hwd, -, -⟩ := S.two_vertices d hd
  have hw : S.rk w = 0 := by have := S.rk_lt_of_lt hwd; omega
  have s1 : ReflTransGen (TriAdj (orderComplex P)) ({v, e, f} : Finset P)
      ({w, d, f} : Finset P) := S.conn_in_face hfe hf hv hve hef hw hwd hdf
  have s2 : ReflTransGen (TriAdj (orderComplex P)) ({w, d, f} : Finset P)
      ({w, d, f'} : Finset P) := by
    by_cases hff' : f = f'
    · subst hff'; exact ReflTransGen.refl
    · exact ReflTransGen.single (triAdj_face hwd hdf hdf' hff')
  have s3 : ReflTransGen (TriAdj (orderComplex P)) ({w, d, f'} : Finset P)
      ({v', e', f'} : Finset P) := S.conn_in_face hfe hf' hw hwd hdf' hv' hv'e' he'f'
  exact (s1.trans s2).trans s3

omit [Fintype P] in
/-- Flags over faces joined by a chain of adjacent faces are connected. -/
theorem conn_along_faces (hfe : FaceEdges S) {f f' : P} (hchain : ReflTransGen (FaceAdj S) f f')
    (hf : S.rk f = 2) {v e v' e' : P}
    (hv : S.rk v = 0) (hve : v < e) (hef : e < f)
    (hv' : S.rk v' = 0) (hv'e' : v' < e') (he'f' : e' < f') :
    ReflTransGen (TriAdj (orderComplex P)) ({v, e, f} : Finset P) ({v', e', f'} : Finset P) := by
  have key : ∀ {b : P}, ReflTransGen (FaceAdj S) f b → ∀ x y : P, S.rk x = 0 → x < y → y < b →
      ReflTransGen (TriAdj (orderComplex P)) ({v, e, f} : Finset P) ({x, y, b} : Finset P) := by
    intro b hb
    induction hb with
    | refl =>
        intro x y hx hxy hyb
        exact S.conn_in_face hfe hf hv hve hef hx hxy hyb
    | @tail c d hfc hcd ih =>
        intro x y hx hxy hyd
        obtain ⟨g, hg, hgc, -⟩ := id hcd
        have hc : S.rk c = 2 := by
          have := S.rk_lt_of_lt hgc
          have := S.rk_le_two c
          omega
        obtain ⟨w, d', hw, hwd', hd'c⟩ := S.exists_flag_of_rk_two hc
        exact (ih w d' hw hwd' hd'c).trans
          (S.conn_face_step hfe hcd hw hwd' hd'c hx hxy hyd)
  exact key hchain v' e' hv' hv'e' he'f'

omit [Fintype P] in
/-- **The dual graph of the order complex is connected.** -/
theorem dual_connected (hfe : FaceEdges S) (hfc : FacesConnected S) :
    ∀ σ σ' : Finset P, IsTri (orderComplex P) σ → IsTri (orderComplex P) σ' →
      ReflTransGen (TriAdj (orderComplex P)) σ σ' := by
  intro σ σ' hσ hσ'
  obtain ⟨v, e, f, hve, hef, rfl⟩ := orderComplex_exists_flag_of_isTri hσ
  obtain ⟨v', e', f', hv'e', he'f', rfl⟩ := orderComplex_exists_flag_of_isTri hσ'
  obtain ⟨hv, -, hf⟩ := S.rk_flag hve hef
  obtain ⟨hv', -, hf'⟩ := S.rk_flag hv'e' he'f'
  exact S.conn_along_faces hfe (hfc f f' hf hf') hf hv hve hef hv' hv'e' he'f'

end SurfaceRank

end ASC

end FiniteChains
