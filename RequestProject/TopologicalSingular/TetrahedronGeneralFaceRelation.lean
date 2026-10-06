module

/-
The horn comparison is adapted from the simplicial telescope argument of
Vasily Ilin, homotopy-groups-lean commit
c66523531ff172d7f41913d94e56921e790a1b47, Hurewicz/SimplicialTelescope.lean,
released under Apache 2.0. In degree two a single telescope stage suffices.
All fillers here are actual continuous singular simplices.
-/
public import RequestProject.TopologicalSingular.TetrahedronLastFaceRelation
public import RequestProject.TopologicalSingular.PointedTriangleHorn

@[expose] public section

namespace FiniteChains.TopologicalSingular
variable {X : Type} [TopologicalSpace X] {x : X}

namespace PointedSingularTriangle

/-- The four actual pi2 classes on the boundary of a based-edge tetrahedron
satisfy the alternating relation, without any assumption that a face is constant. -/
theorem tetrahedron_relation (a b c d : PointedSingularTriangle X x)
    (tau : Simplex X 3)
    (hfaces : ∀ i : Fin 4, face i tau = ![a.map, b.map, c.map, d.map] i) :
    a.pi2 + c.pi2 = b.pi2 + d.pi2 := by
  obtain ⟨U, hU, hedgeU⟩ := pointed_triangle_horn_exists 1
    ![constant x, constant x, c, d]
  let e : PointedSingularTriangle X x := ⟨face 1 U, hedgeU 1⟩
  have hUfaces : ∀ i : Fin 4,
      face i U = ![(constant x).map, e.map, c.map, d.map] i := by
    intro i
    fin_cases i
    · exact hU 0 (by decide)
    · rfl
    · exact hU 2 (by decide)
    · exact hU 3 (by decide)
  have he : e.pi2 + d.pi2 = c.pi2 := first_face_constant_relation e c d U hUfaces
  obtain ⟨W, h0, h1, h2, h3⟩ := singular_four_horn_missing_one
    (singularDegeneracy 0 a.map) tau U (singularDegeneracy 2 d.map)
    (by simp [degeneracy_zero_faces, hfaces])
    (by simp [degeneracy_zero_faces, hUfaces])
    (by simp [degeneracy_zero_faces, degeneracy_two_faces])
    (by simp [hfaces, hUfaces])
    (by simp [hfaces, degeneracy_two_faces])
    (by simp [hUfaces, degeneracy_two_faces])
  have hWfaces : ∀ i : Fin 4,
      face i W = ![a.map, b.map, e.map, (constant x).map] i := by
    intro i
    fin_cases i <;> simp_all [degeneracy_zero_faces, degeneracy_two_faces]
  have hab : a.pi2 + e.pi2 = b.pi2 := last_face_constant_relation a b e W hWfaces
  calc
    a.pi2 + c.pi2 = a.pi2 + (e.pi2 + d.pi2) := by rw [he]
    _ = (a.pi2 + e.pi2) + d.pi2 := (add_assoc _ _ _).symm
    _ = b.pi2 + d.pi2 := by rw [hab]

end PointedSingularTriangle

theorem tetrahedron_pi2_general_face_relation (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x) :
    tetrahedronFacePi2Class tau hedge 0 + tetrahedronFacePi2Class tau hedge 2 =
      tetrahedronFacePi2Class tau hedge 1 + tetrahedronFacePi2Class tau hedge 3 := by
  let a : Fin 4 → PointedSingularTriangle X x := fun i => ⟨face i tau, hedge i⟩
  exact PointedSingularTriangle.tetrahedron_relation (a 0) (a 1) (a 2) (a 3) tau
    (by intro i; fin_cases i <;> rfl)

/-- The alternating boundary of every singular tetrahedron with constant edges
vanishes in the genuine second homotopy group. -/
theorem tetrahedron_pi2_alternating_sum_eq_zero (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x) :
    ∑ i : Fin 4, (-1 : ℤ) ^ (i : ℕ) • tetrahedronFacePi2Class tau hedge i = 0 := by
  have hsum {A : Type} [AddCommGroup A] (f : Fin 4 → A) :
      ∑ i : Fin 4, (-1 : ℤ) ^ (i : ℕ) • f i = (f 0 + f 2) - (f 1 + f 3) := by
    norm_num [Fin.sum_univ_four]
    abel
  rw [hsum (tetrahedronFacePi2Class tau hedge),
    tetrahedron_pi2_general_face_relation tau hedge, sub_self]

end FiniteChains.TopologicalSingular
