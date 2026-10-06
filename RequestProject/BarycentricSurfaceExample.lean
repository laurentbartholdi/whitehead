module

public import RequestProject.BarycentricSurface
public import RequestProject.MomentAngleExample

@[expose] public section

/-!
# A nonempty instance of the subdivision computation

`RequestProject/BarycentricSurface.lean` proves that the barycentric subdivision of a
complex in which every edge lies in exactly two triangles has the same property.  This file
checks that the hypotheses are satisfiable, on the boundary of the tetrahedron — the
simplest triangulated closed surface, already used in
`RequestProject/MomentAngleExample.lean`.
-/

namespace FiniteChains

open Finset

/-- The boundary of the tetrahedron is at most two-dimensional. -/
theorem tetra_dim (s : Finset (Fin 4)) (hs : s ∈ tetraASC.faces) : s.card ≤ 3 := hs

/-- **Every edge of the boundary of the tetrahedron lies in exactly two triangles.** -/
theorem tetra_edgeInTwoTriangles : ASC.EdgeInTwoTriangles tetraASC := by
  intro e _ hcard
  have hdiff : (univ \ e).card = 2 := by
    rw [Finset.card_univ_diff, hcard]
    rfl
  obtain ⟨v₁, v₂, hv, hv2⟩ := Finset.card_eq_two.mp hdiff
  have hmem : ∀ v : Fin 4, v ∉ e ↔ v ∈ ({v₁, v₂} : Finset (Fin 4)) := by
    intro v
    rw [← hv2]
    simp
  have hface : ∀ v : Fin 4, v ∉ e → insert v e ∈ tetraASC.faces := by
    intro v hvv
    show (insert v e).card ≤ 3
    rw [Finset.card_insert_of_notMem hvv, hcard]
  refine ⟨v₁, v₂, hv, ⟨(hmem v₁).2 (by simp), hface _ ((hmem v₁).2 (by simp))⟩,
    ⟨(hmem v₂).2 (by simp), hface _ ((hmem v₂).2 (by simp))⟩, ?_⟩
  intro z hz
  have := (hmem z).1 hz.1
  simpa using this

/-- **The barycentric subdivision of the boundary of the tetrahedron is again a closed
surface**: each of its edges lies in exactly two triangles. -/
theorem tetra_barycentric_edgeInTwoTriangles :
    ASC.EdgeInTwoTriangles tetraASC.barycentric :=
  ASC.barycentric_edgeInTwoTriangles tetraASC tetra_dim tetra_edgeInTwoTriangles

end FiniteChains
