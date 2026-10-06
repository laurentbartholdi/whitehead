module

public import RequestProject.TopologicalSingular.StationaryTriangleNormalization
public import RequestProject.TopologicalSingular.TetrahedronGeneralFaceRelation

@[expose] public section

namespace FiniteChains.TopologicalSingular
variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

noncomputable def stationaryPointedTriangle (x : X) (tau : Simplex X 2) :
    PointedSingularTriangle X x :=
  ⟨stationaryTriangle x tau, stationaryTriangle_face x tau⟩

noncomputable def stationaryPi2Chain (x : X) :
    Chain X 2 →ₗ[ℤ] Additive (HomotopyGroup (Fin 2) X x) :=
  Finsupp.linearCombination ℤ (fun tau => (stationaryPointedTriangle x tau).pi2)

theorem stationaryPi2Chain_single_of_based (x : X) (a : PointedSingularTriangle X x) (r : ℤ) :
    stationaryPi2Chain x (Finsupp.single a.map r) = r • a.pi2 := by
  rw [stationaryPi2Chain, Finsupp.linearCombination_single]
  apply congrArg (fun v : Additive (HomotopyGroup (Fin 2) X x) => r • v)
  apply PointedSingularTriangle.pi2_congr
  exact stationaryTriangle_eq_of_based x a.map a.based

theorem stationaryPi2Chain_basedTriangleCycle (x : X) (a : PointedSingularTriangle X x) :
    stationaryPi2Chain x (basedTriangleCycle a.map x) = a.pi2 := by
  rw [basedTriangleCycle, map_sub, stationaryPi2Chain_single_of_based x a 1]
  have hc := stationaryPi2Chain_single_of_based x (PointedSingularTriangle.constant x) 1
  change stationaryPi2Chain x (Finsupp.single (ContinuousMap.const (Domain 2) x) 1) =
    (1 : ℤ) • (PointedSingularTriangle.constant x).pi2 at hc
  rw [hc, PointedSingularTriangle.constant_pi2, one_smul, smul_zero, sub_zero]

theorem stationaryPi2Chain_boundary_single (x : X) (tau : Simplex X 3) :
    stationaryPi2Chain x (boundary 2 (Finsupp.single tau 1)) = 0 := by
  obtain ⟨T, hT⟩ := stationaryTetrahedron_exists x tau
  have hedge : ∀ (i : Fin 4) (j : Fin 3),
      face j (face i T) = ContinuousMap.const (Domain 1) x := by
    intro i j
    rw [hT, stationaryTriangle_face]
  have h := tetrahedron_pi2_alternating_sum_eq_zero T hedge
  convert h using 1
  rw [boundary_single, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  simp only [stationaryPi2Chain, Finsupp.linearCombination_single, one_smul]
  apply congrArg (fun v : Additive (HomotopyGroup (Fin 2) X x) => (-1 : ℤ) ^ (i : ℕ) • v)
  exact (PointedSingularTriangle.tetrahedron_face_pi2 T hedge i
    (stationaryPointedTriangle x (face i tau)) (hT i)).symm

theorem stationaryPi2Chain_comp_boundary (x : X) :
    (stationaryPi2Chain x).comp (boundary 2) = 0 := by
  apply Finsupp.lhom_ext
  intro tau r
  change stationaryPi2Chain x (boundary 2 (Finsupp.single tau r)) = 0
  have hs : Finsupp.single tau r = r • Finsupp.single tau (1 : ℤ) := by simp
  rw [hs, map_smul, map_smul, stationaryPi2Chain_boundary_single, smul_zero]

theorem stationaryPi2Chain_boundary (x : X) (b : Chain X 3) :
    stationaryPi2Chain x (boundary 2 b) = 0 :=
  DFunLike.congr_fun (stationaryPi2Chain_comp_boundary x) b

end FiniteChains.TopologicalSingular
