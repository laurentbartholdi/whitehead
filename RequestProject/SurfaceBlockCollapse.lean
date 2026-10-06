module

public import RequestProject.SpineCollapse
public import RequestProject.BarycentricConnected
public import RequestProject.BarycentricSurfaceExample

@[expose] public section

/-!
# Lemma 3.2 (ii) for the complex of the paper

The block of Section 3.3 is built from the cube complex `C(L_q)`, where `L_q` is the
barycentric subdivision of a triangulation of the closed surface `Σ_q`.  The three
combinatorial hypotheses of the collapse — every edge in at most two triangles, a connected
dual graph, and every vertex in a triangle — are verified for `L_q` in
`RequestProject/BarycentricSurface.lean` and `RequestProject/BarycentricConnected.lean`.

This file combines them with the collapse itself: for a triangulated closed surface `K`,
all three-cubes of the truncated complex over the barycentric subdivision of `K` are
removed by elementary collapses, leaving a two-dimensional spine.
-/

namespace FiniteChains

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- The closed surface condition gives a triangle through every edge. -/
theorem exists_triangle_of_edge {K : ASC V} (hsurf : ASC.EdgeInTwoTriangles K)
    (e : Finset V) (he : e ∈ K.faces) (hcard : e.card = 2) :
    ∃ t ∈ K.faces, t.card = 3 ∧ e ⊆ t := by
  obtain ⟨v₁, -, -, hv1, -, -⟩ := hsurf e he hcard
  refine ⟨insert v₁ e, hv1.2, ?_, Finset.subset_insert _ _⟩
  rw [Finset.card_insert_of_notMem hv1.1, hcard]

/-- **Lemma 3.2 (ii) for the subdivision of a triangulated closed surface.**  If every face
of `K` has at most three vertices, every edge of `K` lies in exactly two triangles, every
vertex lies in an edge, and the dual graph of `K` is connected, then all three-cubes of the
truncated cube complex over `L = sd K` collapse away. -/
theorem exists_spine_collapse_barycentric (K : ASC V)
    (hdim : ∀ s ∈ K.faces, s.card ≤ 3) (hsurf : ASC.EdgeInTwoTriangles K)
    (hdual : ∀ u u' : Finset V, IsTri K u → IsTri K u' →
      Relation.ReflTransGen (TriAdj K) u u')
    (hvert_edge : ∀ v : V, ({v} : Finset V) ∈ K.faces → ∃ e ∈ K.faces, e.card = 2 ∧ v ∈ e)
    (a₀ : K.Face) :
    ∃ l : List (Cube K.Face),
      Collapse.IsCollapse (spineInc K.barycentric) l (topCubes K.barycentric) := by
  have hcover : ∀ a : K.Face, ∃ σ : Finset K.Face, IsTri K.barycentric σ ∧ a ∈ σ := by
    intro a
    obtain ⟨σ, hface, hcard, hmem⟩ :=
      ASC.barycentric_vertex_in_triangle K hdim
        (fun e he hc => exists_triangle_of_edge hsurf e he hc) hvert_edge a
    exact ⟨σ, ⟨hface, hcard⟩, hmem⟩
  obtain ⟨σ₀, hσ₀, -⟩ := hcover a₀
  exact exists_spine_collapse_of_surface
    (ASC.barycentric_edgeInTwoTriangles K hdim hsurf)
    (fun _ _ h h' => ASC.barycentric_dual_connected hdim hdual h h')
    hcover hσ₀

/-! ### Flag vertex links -/

/-- **Every vertex link of the cube complex over the subdivision is flag.**  This is the
hypothesis of the cubical curvature criterion quoted in Section 3.3: the links of `C(L_q)`
are `L_q`, and `L_q`, being a barycentric subdivision, is flag. -/
theorem linkASC_barycentric_isFlag (K : ASC V) {f : Cube K.Face} (hf : IsVertexCube f) :
    (linkASC K.barycentric f (inMA_of_isVertexCube K.barycentric hf)).IsFlag := by
  intro s hs
  rw [linkASC_eq K.barycentric hf]
  refine ASC.barycentric_isFlag K s ?_
  intro t ht hc
  have hts := hs t ht hc
  rwa [linkASC_eq K.barycentric hf] at hts

/-! ### A nonempty instance: the boundary of the tetrahedron -/

/-- Every vertex of the boundary of the tetrahedron lies in an edge. -/
theorem tetra_vert_edge (v : Fin 4) (_ : ({v} : Finset (Fin 4)) ∈ tetraASC.faces) :
    ∃ e ∈ tetraASC.faces, e.card = 2 ∧ v ∈ e := by
  refine ⟨{v, v + 1}, ?_, ?_, by simp⟩
  · show ({v, v + 1} : Finset (Fin 4)).card ≤ 3
    exact (Finset.card_insert_le _ _).trans (by simp)
  · have hne : ∀ u : Fin 4, u ≠ u + 1 := by decide
    exact Finset.card_pair (hne v)

/-- **Lemma 3.2 (ii) for the subdivision of the boundary of the tetrahedron.** -/
theorem tetra_spine_collapse_barycentric :
    ∃ l : List (Cube tetraASC.Face),
      Collapse.IsCollapse (spineInc tetraASC.barycentric) l (topCubes tetraASC.barycentric) :=
  exists_spine_collapse_barycentric tetraASC tetra_dim tetra_edgeInTwoTriangles tetra_dual
    tetra_vert_edge ⟨{0}, by show ({0} : Finset (Fin 4)).card ≤ 3; decide, ⟨0, by simp⟩⟩

end FiniteChains
