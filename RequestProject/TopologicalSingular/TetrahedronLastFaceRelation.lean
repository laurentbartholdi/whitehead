/-
The explicit four-horn index shift is adapted from the simplicial index-shift
argument of Vasily Ilin, homotopy-groups-lean commit
c66523531ff172d7f41913d94e56921e790a1b47, Hurewicz/SimplicialIndexShift.lean,
released under Apache 2.0. Here it is specialized to actual singular triangles
and to the previously checked cubical model of pi2.
-/
import RequestProject.TopologicalSingular.SingularFourHorn
import RequestProject.TopologicalSingular.PointedSingularTriangle

namespace FiniteChains.TopologicalSingular.PointedSingularTriangle
variable {X : Type} [TopologicalSpace X] {x : X}

/-- Move the constant face from the last index to the first using a genuine
four-dimensional horn filling, and apply the cubical multiplication relation. -/
theorem last_face_constant_relation (a b c : PointedSingularTriangle X x)
    (tau : Simplex X 3)
    (hfaces : ∀ i : Fin 4,
      face i tau = ![a.map, b.map, c.map, (constant x).map] i) :
    a.pi2 + c.pi2 = b.pi2 := by
  obtain ⟨W, h0, h1, h2, h3⟩ := singular_four_horn_missing_one
    (singularDegeneracy 2 a.map) (singularDegeneracy 1 c.map)
    tau (singularDegeneracy 0 a.map)
    (by simp [degeneracy_two_faces, degeneracy_one_faces])
    (by simp [degeneracy_two_faces, hfaces])
    (by simp [degeneracy_two_faces, degeneracy_zero_faces])
    (by simp [degeneracy_one_faces, hfaces])
    (by simp [degeneracy_one_faces, degeneracy_zero_faces])
    (by simp [hfaces, degeneracy_zero_faces])
  have hW : ∀ i : Fin 4,
      face i W = ![(constant x).map, c.map, b.map, a.map] i := by
    intro i
    fin_cases i <;> simp_all [degeneracy_two_faces, degeneracy_one_faces,
      degeneracy_zero_faces]
  have h := first_face_constant_relation c b a W hW
  exact (add_comm a.pi2 c.pi2).trans h

end FiniteChains.TopologicalSingular.PointedSingularTriangle
