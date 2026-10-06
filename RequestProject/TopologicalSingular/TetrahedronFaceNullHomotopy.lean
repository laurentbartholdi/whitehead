module

public import RequestProject.TopologicalSingular.BasedTriangleHomotopy
public import RequestProject.TopologicalSingular.SimplexFaceIntersections

@[expose] public section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

theorem singularSimplex_eq_of_zero_coordinate {n : ℕ} (tau : Simplex X (n + 1))
    (i : Fin (n + 2)) (hface : face i tau = ContinuousMap.const (Domain n) x)
    (z : Domain (n + 1)) (hz : z.val i = 0) : tau z = x := by
  obtain ⟨w, hw⟩ := domain_zero_coordinate_face z i hz
  have he := congrArg (fun f : Simplex X n => f w) hface
  simpa only [face_apply, hw, ContinuousMap.const_apply] using he

noncomputable def tetrahedronFace3Embedding : C(Domain 2, Domain 3) :=
  ⟨stdSimplex.map (SimplexCategory.δ (3 : Fin 4)), stdSimplex.continuous_map _⟩

theorem tetrahedronFace3Embedding_coordinate (z : Domain 2) (i : Fin 3) :
    (tetrahedronFace3Embedding z).val i.castSucc = z.val i := by
  have he := simplex_face_coordinate_succAbove (3 : Fin 4) z i
  have hi : (3 : Fin 4).succAbove i = i.castSucc := by fin_cases i <;> rfl
  rwa [hi] at he

noncomputable def tetrahedronFace3Cone :
    tetrahedronFace3Embedding.Homotopy (ContinuousMap.const (Domain 2) (stdSimplex.vertex (3 : Fin 4))) :=
  simplexLinearHomotopy tetrahedronFace3Embedding (ContinuousMap.const (Domain 2) (stdSimplex.vertex 3))

theorem tetrahedronFace3Cone_zero_coordinate (t : I) (z : Domain 2)
    (i : Fin 3) (hi : z.val i = 0) : (tetrahedronFace3Cone (t, z)).val i.castSucc = 0 := by
  change (1 - (t : ℝ)) * (tetrahedronFace3Embedding z).val i.castSucc +
    (t : ℝ) * (stdSimplex.vertex (3 : Fin 4)).val i.castSucc = 0
  rw [tetrahedronFace3Embedding_coordinate, hi]
  have hv : (stdSimplex.vertex (3 : Fin 4) : Domain 3).val i.castSucc = 0 := by fin_cases i <;> rfl
  rw [hv]
  ring

theorem tetrahedronFace3_based (tau : Simplex X 3)
    (hother : ∀ i : Fin 3, face i.castSucc tau = ContinuousMap.const (Domain 2) x)
    (j : Fin 3) : face j (face 3 tau) = ContinuousMap.const (Domain 1) x := by
  apply ContinuousMap.ext
  intro z
  apply singularSimplex_eq_of_zero_coordinate tau j.castSucc (hother j)
  change (tetrahedronFace3Embedding (stdSimplex.map (SimplexCategory.δ j) z)).val j.castSucc = 0
  rw [tetrahedronFace3Embedding_coordinate]
  exact simplex_face_coordinate_zero j z

/-- If the other three faces of a tetrahedron are constant, its last face
contracts relative to its full boundary by coning to the opposite vertex. -/
noncomputable def tetrahedronFace3NullHomotopy (tau : Simplex X 3)
    (hother : ∀ i : Fin 3, face i.castSucc tau = ContinuousMap.const (Domain 2) x) :
    ContinuousMap.HomotopyRel (face 3 tau) (ContinuousMap.const (Domain 2) x) (simplexBoundary 2) where
  toFun w := tau (tetrahedronFace3Cone w)
  continuous_toFun := tau.continuous.comp tetrahedronFace3Cone.continuous
  map_zero_left z := by
    rw [tetrahedronFace3Cone.apply_zero]
    rfl
  map_one_left z := by
    rw [tetrahedronFace3Cone.apply_one]
    apply singularSimplex_eq_of_zero_coordinate tau (0 : Fin 4) (hother 0)
    rfl
  prop' t z hz := by
    obtain ⟨i, hi⟩ := hz
    have hstart : face 3 tau z = x := by
      apply singularSimplex_eq_of_zero_coordinate tau i.castSucc (hother i)
      exact (tetrahedronFace3Embedding_coordinate z i).trans hi
    rw [hstart]
    exact singularSimplex_eq_of_zero_coordinate tau i.castSucc (hother i) _
      (tetrahedronFace3Cone_zero_coordinate t z i hi)

theorem tetrahedronFace3_square_nullhomotopic (tau : Simplex X 3)
    (hother : ∀ i : Fin 3, face i.castSucc tau = ContinuousMap.const (Domain 2) x) :
    GenLoop.Homotopic (basedTriangleSquare (face 3 tau) (tetrahedronFace3_based tau hother)) GenLoop.const :=
  basedTriangleSquare_nullhomotopic _ _ (tetrahedronFace3NullHomotopy tau hother)

theorem tetrahedronFace3_pi2_eq_one (tau : Simplex X 3)
    (hother : ∀ i : Fin 3, face i.castSucc tau = ContinuousMap.const (Domain 2) x) :
    (Quotient.mk _ (basedTriangleSquare (face 3 tau) (tetrahedronFace3_based tau hother)) :
      HomotopyGroup (Fin 2) X x) = (1 : HomotopyGroup (Fin 2) X x) := by
  rw [HomotopyGroup.one_def]
  exact Quotient.sound (tetrahedronFace3_square_nullhomotopic tau hother)

end FiniteChains.TopologicalSingular
