import RequestProject.MomentAngleConnected

/-!
# A nonempty instance of the cube-complex computation

The results of `RequestProject/MomentAngle.lean` and `RequestProject/TruncatedCube.lean` are
proved for an arbitrary simplicial cycle `o`.  To show that they are not proved vacuously,
this file exhibits the simplest oriented triangulated closed surface: the boundary of the
tetrahedron, on the vertex set `Fin 4`.  Its fundamental cycle is checked by computation,
and the corresponding cubical chain of `C(L)` is shown to be nonzero.
-/

namespace FiniteChains

open Finset

/-- The two-skeleton of the tetrahedron: all subsets of `Fin 4` with at most three
vertices. -/
def tetraASC : ASC (Fin 4) where
  faces := {s : Finset (Fin 4) | s.card ≤ 3}
  empty_mem := by simp
  down_closed := fun hs hts => le_trans (Finset.card_le_card hts) hs

/-- Every vertex link of the cube complex `C(L)` of this example is `L` itself. -/
theorem tetra_link {f : Cube (Fin 4)} (hf : IsVertexCube f) :
    (linkASC tetraASC f (inMA_of_isVertexCube tetraASC hf)).faces = tetraASC.faces :=
  linkASC_eq tetraASC hf

/-- The fundamental cycle of the boundary of the tetrahedron: the triangle omitting the
vertex `k` gets the sign `(-1)^k`. -/
def tetraOrient : Finset (Fin 4) → ℤ := fun s =>
  if s = {1, 2, 3} then 1
  else if s = {0, 2, 3} then -1
  else if s = {0, 1, 3} then 1
  else if s = {0, 1, 2} then -1
  else 0

/-- The orientation coefficients are supported on the triangles. -/
theorem tetraOrient_support (s : Finset (Fin 4)) (hs : s.card ≠ 3) : tetraOrient s = 0 := by
  revert hs
  revert s
  decide

/-- **The chosen coefficients form a simplicial cycle.** -/
theorem tetraOrient_cycle : simpBdry tetraOrient = 0 := by
  funext τ
  revert τ
  decide

/-- The corresponding cubical chain of `C(L)` is nonzero: the cube with free set
`{1, 2, 3}` and remaining coordinate `+1` has coefficient `1`. -/
theorem tetra_cubeChain_ne_zero : cubeChain tetraOrient (posCube {1, 2, 3}) = 1 := by
  rw [cubeChain_posCube]
  decide

/-- The signed sum of the three-cubes of `C(L)` is a nonzero cubical cycle. -/
theorem tetra_cubeChain_cycle : bdry (cubeChain tetraOrient) = 0 :=
  cubeChain_cycle tetraOrient_cycle

/-- Lemma 3.2 (iii) for this example: in the truncated complex the fundamental cycle of the
cut surface is a boundary. -/
theorem tetra_cutSurface_isBoundary :
    bdryT (cubeChain tetraOrient, 0) = (0, -tetraOrient) :=
  cutSurface_isBoundary tetraOrient_cycle tetraOrient_support

/-! ### The hypotheses of the connectivity theorem are satisfiable -/

theorem tetra_isTri_iff {σ : Finset (Fin 4)} : IsTri tetraASC σ ↔ σ.card = 3 := by
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨show σ.card ≤ 3 by rw [h], h⟩

/-- The dual graph of the boundary of the tetrahedron is connected: any two of its four
triangles share an edge. -/
theorem tetra_dual : ∀ σ σ' : Finset (Fin 4), IsTri tetraASC σ → IsTri tetraASC σ' →
    Relation.ReflTransGen (TriAdj tetraASC) σ σ' := by
  intro σ σ' hσ hσ'
  by_cases hEq : σ = σ'
  · rw [hEq]
  · have key : ∀ s t : Finset (Fin 4), s.card = 3 → t.card = 3 → s ≠ t →
        (s ∩ t).card = 2 := by decide
    exact Relation.ReflTransGen.single ⟨hσ, hσ', key σ σ' hσ.2 hσ'.2 hEq⟩

/-- Every vertex lies in a triangle. -/
theorem tetra_cover : ∀ v : Fin 4, ∃ σ : Finset (Fin 4), IsTri tetraASC σ ∧ v ∈ σ := by
  intro v
  refine ⟨Finset.univ.erase (if v = 0 then 1 else 0), tetra_isTri_iff.2 ?_, ?_⟩
  · revert v; decide
  · revert v; decide

/-- **The adjacency graph of the three-cubes of `C(L)` is connected** in this example. -/
theorem tetra_connected {f g : Cube (Fin 4)} (hf : IsTri tetraASC (freeSet f))
    (hg : IsTri tetraASC (freeSet g)) :
    Relation.ReflTransGen (Move tetraASC) f g :=
  reflTransGen_move tetra_dual tetra_cover hf hg

end FiniteChains
