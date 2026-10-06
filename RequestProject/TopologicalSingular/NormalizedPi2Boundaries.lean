module

public import RequestProject.TopologicalSingular.TetrahedronGeneralFaceRelation
public import RequestProject.TopologicalSingular.CoherentTetrahedronNormalization
public import RequestProject.TopologicalSingular.HurewiczSurjectivity

@[expose] public section

namespace FiniteChains.TopologicalSingular
variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem normalizedPi2Chain_boundary_single (x : X) (tau : Simplex X 3) :
    normalizedPi2Chain x (boundary 2 (Finsupp.single tau 1)) = 0 := by
  have h := tetrahedron_pi2_alternating_sum_eq_zero
    (normalizedTetrahedron x tau) (normalizedTetrahedron_edge x tau)
  convert h using 1
  rw [boundary_single, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  simp only [normalizedPi2Chain, Finsupp.linearCombination_single, one_smul]
  apply congrArg (fun v : Additive (HomotopyGroup (Fin 2) X x) => (-1 : ℤ) ^ (i : ℕ) • v)
  exact (PointedSingularTriangle.tetrahedron_face_pi2
    (normalizedTetrahedron x tau) (normalizedTetrahedron_edge x tau) i
    ⟨normalizedTriangle x (face i tau), normalizedTriangle_face x (face i tau)⟩
    (normalizedTetrahedron_face x tau i)).symm

theorem normalizedPi2Chain_comp_boundary (x : X) :
    (normalizedPi2Chain x).comp (boundary 2) = 0 := by
  apply Finsupp.lhom_ext
  intro tau r
  change normalizedPi2Chain x (boundary 2 (Finsupp.single tau r)) = 0
  have hs : Finsupp.single tau r = r • Finsupp.single tau (1 : ℤ) := by simp
  rw [hs, map_smul, map_smul, normalizedPi2Chain_boundary_single, smul_zero]

/-- The sum of normalized based triangles kills every actual singular 3-boundary. -/
theorem normalizedPi2Chain_boundary (x : X) (b : Chain X 3) :
    normalizedPi2Chain x (boundary 2 b) = 0 :=
  DFunLike.congr_fun (normalizedPi2Chain_comp_boundary x) b

theorem normalizedPi2Chain_eq_of_homologous (x : X) (c d : Chain X 2)
    (h : c - d ∈ LinearMap.range (boundary 2)) :
    normalizedPi2Chain x c = normalizedPi2Chain x d := by
  obtain ⟨b, hb⟩ := h
  have he := normalizedPi2Chain_boundary x b
  rw [hb, map_sub] at he
  exact sub_eq_zero.mp he

end FiniteChains.TopologicalSingular
