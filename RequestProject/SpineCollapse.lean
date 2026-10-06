import RequestProject.Collapse
import RequestProject.BarycentricSurface
import RequestProject.MomentAngleExample

/-!
# Lemma 3.2 (ii) for the explicit model: the three-cubes of `C(L)` collapse away

`RequestProject/Collapse.lean` proves the combinatorial collapse argument of Lemma 3.2 (ii)
in the abstract: if every codimension one face lies in at most two top cells, the adjacency
graph of the top cells is connected, and one top cell has a free face, then all top cells
can be removed by elementary collapses.  `RequestProject/MomentAngleConnected.lean` proves
the connectivity of the adjacency graph for the cube complex `C(L)`.

This file puts the two together for the truncated complex

  `M = C(L) ∖ (open neighbourhood of the corner (1, …, 1))`,

and so proves the statement of the paper in the model at hand: *all three-cells of `M`
disappear under elementary collapses, leaving a two-dimensional spine.*

The cells are those of `RequestProject/MomentAngle.lean`.  The codimension one faces used
by the collapse are of two kinds:

* the squares of `C(L)`, each of which lies in at most two three-cubes as soon as every
  edge of `L` lies in at most two triangles (`FiniteChains.card_cofaces`);
* the cut faces created by the truncation: the corner `(1, …, 1)` lies exactly in the
  cubes `posCube σ` (`σ` a triangle of `L`), and truncating cuts each of them along one
  new triangular face, which therefore belongs to that cube only.  These are the faces
  "meeting the cut surface" at which the paper roots its spanning tree.

The hypotheses on `L` are the two combinatorial properties of a triangulated closed
surface used in the paper: every edge lies in at most two triangles, the dual graph is
connected, and every vertex lies in a triangle.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open Finset

instance : Fintype CubeCoord :=
  ⟨{CubeCoord.free, CubeCoord.pos, CubeCoord.neg}, fun x => by cases x <;> decide⟩

variable {V : Type} [Fintype V] [DecidableEq V]

open scoped Classical in
/-- The three-cubes of `C(L)`: the top cells of the complex. -/
noncomputable def topCubes (L : ASC V) : Finset (Cube V) :=
  univ.filter fun f => IsTri L (freeSet f)

open scoped Classical in
@[simp] theorem mem_topCubes {L : ASC V} {f : Cube V} :
    f ∈ topCubes L ↔ IsTri L (freeSet f) := by
  simp [topCubes]

open scoped Classical in
/-- The codimension one faces used in the collapse of `M`, and the three-cubes containing
each of them: a square `g` lies in its cofaces, and the cut face attached to the truncated
corner cube over a triangle `σ` lies in that cube alone. -/
noncomputable def spineInc (L : ASC V) : Cube V ⊕ Finset V → Finset (Cube V)
  | Sum.inl g => if (freeSet g).card = 2 then cofaces L g else ∅
  | Sum.inr σ => if IsTri L σ then {posCube σ} else ∅

open scoped Classical in
/-- **Every codimension one face lies in at most two three-cubes.**  For squares this is the
incidence count of Lemma 3.2 ("every square meets exactly two three-cubes, because every
edge of `L` meets two triangles"); a cut face lies in the single cube it truncates. -/
theorem spineInc_card_le_two {L : ASC V}
    (hedge : ∀ e : Finset V, e.card = 2 →
      ((univ.filter fun j => j ∉ e).filter fun j => insert j e ∈ L.faces).card ≤ 2)
    (f : Cube V ⊕ Finset V) : (spineInc L f).card ≤ 2 := by
  classical
  cases f with
  | inl g =>
      by_cases hg : (freeSet g).card = 2
      · simp only [spineInc, if_pos hg]
        rw [card_cofaces]
        exact hedge _ hg
      · simp [spineInc, hg]
  | inr σ =>
      by_cases hσ : IsTri L σ
      · simp [spineInc, hσ]
      · simp [spineInc, hσ]

/-- A move keeps a cube among the three-cubes: it exchanges one free coordinate for
another, so the dimension is unchanged. -/
theorem mem_topCubes_of_move {L : ASC V} {f g : Cube V} (h : Move L f g)
    (hf : f ∈ topCubes L) : g ∈ topCubes L := by
  classical
  obtain ⟨c, c', hcc, hfc, hfc', hgc, hgc', hagree, -, hgL⟩ := h
  rw [mem_topCubes] at hf ⊢
  refine ⟨hgL, ?_⟩
  -- `freeSet g = insert c' ((freeSet f).erase c)`
  have hset : freeSet g = insert c' ((freeSet f).erase c) := by
    ext v
    simp only [mem_freeSet, Finset.mem_insert, Finset.mem_erase]
    constructor
    · intro hv
      by_cases hvc' : v = c'
      · exact Or.inl hvc'
      · have hvc : v ≠ c := by
          rintro rfl
          exact hgc hv
        exact Or.inr ⟨hvc, by rw [hagree v hvc hvc']; exact hv⟩
    · rintro (rfl | ⟨hvc, hv⟩)
      · exact hgc'
      · by_cases hvc' : v = c'
        · subst hvc'
          exact absurd hv hfc'
        · rw [← hagree v hvc hvc']; exact hv
  have hc : c ∈ freeSet f := by simpa using hfc
  have hc' : c' ∉ (freeSet f).erase c := by
    simp only [Finset.mem_erase, mem_freeSet, not_and]
    intro _
    exact hfc'
  rw [hset, Finset.card_insert_of_notMem hc', Finset.card_erase_of_mem hc, hf.2]

/-- **A move is an adjacency of the collapse**: the two cubes are distinct and share a
square. -/
theorem adj_of_move {L : ASC V} {f g : Cube V} (h : Move L f g)
    (hf : f ∈ topCubes L) (hg : g ∈ topCubes L) :
    Collapse.Adj (spineInc L) f g := by
  classical
  obtain ⟨s, ⟨j, hsj, hfs⟩, ⟨k, hsk, hgs⟩⟩ := h.shares_square
  have hfree : freeSet f = insert j (freeSet s) := by
    rw [hfs, freeSet_update_free]
  have hjs : j ∉ freeSet s := by simpa using hsj
  have hcard : (freeSet s).card = 2 := by
    have := (mem_topCubes.1 hf).2
    rw [hfree, Finset.card_insert_of_notMem hjs] at this
    omega
  have hne : f ≠ g := by
    obtain ⟨c, c', hcc, hfc, hfc', hgc, hgc', -, -, -⟩ := h
    intro hfg
    rw [hfg] at hfc
    exact hgc hfc
  refine ⟨hne, Sum.inl s, ?_, ?_⟩
  · simp only [spineInc, if_pos hcard]
    exact mem_cofaces.2 ⟨j, hsj, by rw [← hfree]; exact (mem_topCubes.1 hf).1, hfs⟩
  · simp only [spineInc, if_pos hcard]
    refine mem_cofaces.2 ⟨k, hsk, ?_, hgs⟩
    have : freeSet g = insert k (freeSet s) := by rw [hgs, freeSet_update_free]
    rw [← this]
    exact (mem_topCubes.1 hg).1

/-- **The adjacency graph of the three-cubes of `C(L)` is connected**, in the form required
by the collapse theorem. -/
theorem connected_topCubes {L : ASC V}
    (hdual : ∀ σ σ', IsTri L σ → IsTri L σ' → Relation.ReflTransGen (TriAdj L) σ σ')
    (hcover : ∀ v : V, ∃ σ, IsTri L σ ∧ v ∈ σ) :
    Collapse.Connected (spineInc L) (topCubes L) := by
  classical
  intro f hf g hg
  have hpath : Relation.ReflTransGen (Move L) f g :=
    reflTransGen_move hdual hcover (mem_topCubes.1 hf) (mem_topCubes.1 hg)
  -- transport the path to the relation restricted to the three-cubes
  have key : ∀ {a b : Cube V}, Relation.ReflTransGen (Move L) a b → a ∈ topCubes L →
      b ∈ topCubes L ∧ Relation.ReflTransGen
        (fun x y => x ∈ topCubes L ∧ y ∈ topCubes L ∧ Collapse.Adj (spineInc L) x y) a b := by
    intro a b hab ha
    induction hab with
    | refl => exact ⟨ha, Relation.ReflTransGen.refl⟩
    | tail hxy hyz ih =>
        obtain ⟨hy, hpath'⟩ := ih
        have hz := mem_topCubes_of_move hyz hy
        exact ⟨hz, hpath'.tail ⟨hy, hz, adj_of_move hyz hy hz⟩⟩
  exact (key hpath hf).2

/-- The cut face of the truncated corner cube over a triangle `σ` is free: that cube is the
only three-cube containing it. -/
theorem hasFreeFace_posCube {L : ASC V} {σ : Finset V} (hσ : IsTri L σ) :
    Collapse.HasFreeFace (spineInc L) (topCubes L) (posCube σ) := by
  classical
  refine ⟨Sum.inr σ, ?_⟩
  have hmem : posCube σ ∈ topCubes L := by
    rw [mem_topCubes, freeSet_posCube]
    exact hσ
  simp only [Collapse.IsFree, spineInc, if_pos hσ]
  ext x
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨rfl, -⟩; rfl
  · rintro rfl; exact ⟨rfl, hmem⟩

open scoped Classical in
/-- **Lemma 3.2 (ii) in the explicit model.**  For a simplicial complex `L` each of whose
edges lies in at most two triangles, whose dual graph is connected and each of whose
vertices lies in a triangle, all three-cubes of the truncated complex
`M = C(L) ∖ (neighbourhood of the corner)` can be removed by elementary collapses: the
spanning-tree argument of the paper is carried out, and `M` collapses onto a
two-dimensional spine. -/
theorem exists_spine_collapse {L : ASC V}
    (hedge : ∀ e : Finset V, e.card = 2 →
      ((univ.filter fun j => j ∉ e).filter fun j => insert j e ∈ L.faces).card ≤ 2)
    (hdual : ∀ σ σ', IsTri L σ → IsTri L σ' → Relation.ReflTransGen (TriAdj L) σ σ')
    (hcover : ∀ v : V, ∃ σ, IsTri L σ ∧ v ∈ σ)
    {σ₀ : Finset V} (hσ₀ : IsTri L σ₀) :
    ∃ l : List (Cube V), Collapse.IsCollapse (spineInc L) l (topCubes L) := by
  classical
  refine Collapse.exists_isCollapse_of_connected (spineInc_card_le_two hedge)
    (connected_topCubes hdual hcover) (t₀ := posCube σ₀) ?_ (hasFreeFace_posCube hσ₀)
  rw [mem_topCubes, freeSet_posCube]
  exact hσ₀

/-! ### The incidence hypothesis from the closed surface condition -/

open scoped Classical in
/-- If every edge of `L` lies in exactly two triangles, then the incidence hypothesis of the
collapse holds: an edge is enlarged to a triangle by at most two vertices.  (An `e` which is
not a face of `L` is enlarged by none.) -/
theorem hedge_of_edgeInTwoTriangles {L : ASC V} (h : ASC.EdgeInTwoTriangles L)
    (e : Finset V) (he : e.card = 2) :
    ((univ.filter fun j => j ∉ e).filter fun j => insert j e ∈ L.faces).card ≤ 2 := by
  classical
  by_cases hef : e ∈ L.faces
  · obtain ⟨v₁, v₂, -, -, -, huniq⟩ := h e hef he
    refine le_trans (Finset.card_le_card (?_ : _ ⊆ ({v₁, v₂} : Finset V))) (by
      simpa only [Finset.card_singleton] using Finset.card_insert_le v₁ {v₂})
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rcases huniq j ⟨hj.1, hj.2⟩ with rfl | rfl <;> simp
  · have : ((univ.filter fun j => j ∉ e).filter fun j => insert j e ∈ L.faces) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 ?_
      intro j _ hcon
      exact hef (L.down_closed hcon (Finset.subset_insert _ _))
    rw [this]
    simp

open scoped Classical in
/-- **The collapse of Lemma 3.2 (ii) for a closed surface `L`.**  This is
`FiniteChains.exists_spine_collapse` with the incidence hypothesis replaced by the closed
surface condition itself. -/
theorem exists_spine_collapse_of_surface {L : ASC V} (hsurf : ASC.EdgeInTwoTriangles L)
    (hdual : ∀ σ σ', IsTri L σ → IsTri L σ' → Relation.ReflTransGen (TriAdj L) σ σ')
    (hcover : ∀ v : V, ∃ σ, IsTri L σ ∧ v ∈ σ)
    {σ₀ : Finset V} (hσ₀ : IsTri L σ₀) :
    ∃ l : List (Cube V), Collapse.IsCollapse (spineInc L) l (topCubes L) :=
  exists_spine_collapse (hedge_of_edgeInTwoTriangles hsurf) hdual hcover hσ₀

/-! ### A nonempty instance: the boundary of the tetrahedron -/

open scoped Classical in
/-- Every edge of the boundary of the tetrahedron lies in at most two triangles. -/
theorem tetra_hedge (e : Finset (Fin 4)) (he : e.card = 2) :
    ((univ.filter fun j => j ∉ e).filter fun j => insert j e ∈ tetraASC.faces).card ≤ 2 := by
  have hcompl : (univ.filter fun j => j ∉ e) = univ \ e := by
    ext j; simp
  calc ((univ.filter fun j => j ∉ e).filter fun j => insert j e ∈ tetraASC.faces).card
      ≤ (univ.filter fun j => j ∉ e).card := Finset.card_filter_le _ _
    _ = 2 := by
        rw [hcompl, Finset.card_univ_diff, he]
        rfl

open scoped Classical in
/-- **Lemma 3.2 (ii) for the boundary of the tetrahedron**: all three-cubes of the truncated
complex `C(L) ∖ (neighbourhood of the corner)` collapse away. -/
theorem tetra_spine_collapse :
    ∃ l : List (Cube (Fin 4)),
      Collapse.IsCollapse (spineInc tetraASC) l (topCubes tetraASC) :=
  exists_spine_collapse tetra_hedge tetra_dual tetra_cover
    (σ₀ := ({1, 2, 3} : Finset (Fin 4))) (tetra_isTri_iff.2 (by decide))

end FiniteChains
