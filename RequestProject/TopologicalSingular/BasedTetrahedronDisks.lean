import RequestProject.TopologicalSingular.TetrahedronSquareDisks
import RequestProject.TopologicalSingular.SimplexLinearHomotopy

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

theorem basedTetrahedron_eq_of_two_zero_coordinates (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x)
    (z : Domain 3) (i j : Fin 4) (hij : i ≠ j) (hi : z.val i = 0) (hj : z.val j = 0) :
    tau z = x := by
  obtain ⟨w, hw⟩ := domain_zero_coordinate_face z i hi
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
  have hz : w.val k = 0 := by
    rw [← simplex_face_coordinate_succAbove i w k, hk, hw, hj]
  obtain ⟨q, hq⟩ := domain_zero_coordinate_face w k hz
  have he := congrArg (fun f : Simplex X 1 => f q) (hedge i k)
  simpa only [face_apply, hq, hw, ContinuousMap.const_apply] using he

theorem tetrahedronDisk03_boundary_two_zeros (z : Fin 2 → I)
    (hz : z ∈ Cube.boundary (Fin 2)) :
    ∃ i j : Fin 4, i ≠ j ∧ (tetrahedronDisk03 z).val i = 0 ∧ (tetrahedronDisk03 z).val j = 0 := by
  obtain ⟨i, hi⟩ := hz
  fin_cases i <;> rcases hi with hi | hi
  all_goals dsimp at hi
  · refine ⟨1, 3, by decide, ?_, ?_⟩ <;>
      simp [tetrahedronDisk03, hi, (z 1).property.1]
  · refine ⟨0, 2, by decide, ?_, ?_⟩ <;>
      simp [tetrahedronDisk03, hi, (z 1).property.2]
  · refine ⟨2, 3, by decide, ?_, ?_⟩ <;>
      simp [tetrahedronDisk03, hi, (z 0).property.1]
  · refine ⟨0, 1, by decide, ?_, ?_⟩ <;>
      simp [tetrahedronDisk03, hi, (z 0).property.2]

noncomputable def basedTetrahedronDisk03 (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x) : GenLoop (Fin 2) X x :=
  ⟨tau.comp tetrahedronDisk03, by
    intro z hz
    obtain ⟨i, j, hij, hi, hj⟩ := tetrahedronDisk03_boundary_two_zeros z hz
    exact basedTetrahedron_eq_of_two_zero_coordinates tau hedge _ i j hij hi hj⟩

noncomputable def basedTetrahedronDisk12 (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x) : GenLoop (Fin 2) X x :=
  ⟨tau.comp tetrahedronDisk12, by
    intro z hz
    change tau (tetrahedronDisk12 z) = x
    rw [← tetrahedronDisks_boundary_eq z hz]
    exact GenLoop.boundary (basedTetrahedronDisk03 tau hedge) z hz⟩

/-- Sweeping through the solid tetrahedron gives a genuine based homotopy
between its two pairs of faces. No homology comparison enters this statement. -/
theorem basedTetrahedronDisks_homotopic (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x) :
    GenLoop.Homotopic (basedTetrahedronDisk03 tau hedge) (basedTetrahedronDisk12 tau hedge) :=
  ⟨(simplexLinearHomotopyRel tetrahedronDisk03 tetrahedronDisk12 (Cube.boundary (Fin 2))
    tetrahedronDisks_boundary_eq).compContinuousMap tau⟩

theorem basedTetrahedronDisks_pi2_eq (tau : Simplex X 3)
    (hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i tau) = ContinuousMap.const (Domain 1) x) :
    (Quotient.mk _ (basedTetrahedronDisk03 tau hedge) : HomotopyGroup (Fin 2) X x) =
      Quotient.mk _ (basedTetrahedronDisk12 tau hedge) :=
  Quotient.sound (basedTetrahedronDisks_homotopic tau hedge)

end FiniteChains.TopologicalSingular
