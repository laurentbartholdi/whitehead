module

public import RequestProject.TopologicalSingular.SimplexBoundaryGluing
public import RequestProject.TopologicalSingular.SingularEdgeNullHomotopy

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ}

theorem simplex_face_coordinate_succAbove (i : Fin (n + 2)) (z : Domain n) (j : Fin (n + 1)) :
    (stdSimplex.map (SimplexCategory.δ i) z).val (i.succAbove j) = z.val j := by
  change (FunOnFinite.linearMap ℝ ℝ i.succAbove z.val) (i.succAbove j) = z.val j
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter]

theorem simplex_face_injective (i : Fin (n + 2)) :
    Function.Injective (stdSimplex.map (SimplexCategory.δ i) : Domain n → Domain (n + 1)) := by
  intro z w h
  apply Subtype.ext
  funext j
  have he := congrArg (fun v : Domain (n + 1) => v.val (i.succAbove j)) h
  simpa only [simplex_face_coordinate_succAbove] using he

/-- A point common to two different faces is on the boundary of each face. -/
theorem simplex_face_intersection_boundary (i j : Fin (n + 2)) (hij : i ≠ j)
    (z w : Domain n)
    (h : stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w) :
    z ∈ simplexBoundary n ∧ w ∈ simplexBoundary n := by
  have one (i j : Fin (n + 2)) (hij : i ≠ j) (z w : Domain n)
      (h : stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w) :
      z ∈ simplexBoundary n := by
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
    refine ⟨k, ?_⟩
    rw [← simplex_face_coordinate_succAbove i z k, hk, h]
    exact simplex_face_coordinate_zero j w
  exact ⟨one i j hij z w h, one j i hij.symm w z h.symm⟩

/-- Relative homotopies of all faces agree automatically on intersections
when they start at the faces of the same simplex. -/
theorem relative_face_homotopies_coherent (tau : Simplex X (n + 1))
    (g : Fin (n + 2) → Simplex X n)
    (H : ∀ i, ContinuousMap.HomotopyRel (face i tau) (g i) (simplexBoundary n))
    (i j : Fin (n + 2)) (t : I) (z w : Domain n)
    (h : stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w) :
    H i (t, z) = H j (t, w) := by
  by_cases hij : i = j
  · subst j
    rw [simplex_face_injective i h]
  · obtain ⟨hz, hw⟩ := simplex_face_intersection_boundary i j hij z w h
    rw [(H i).eq_fst t hz, (H j).eq_fst t hw, face_apply, face_apply, h]

/-- If all vertices of a singular triangle are at the basepoint in a
simply connected target, it can be deformed so that all its edges are
constant. This is an actual continuous homotopy of the entire triangle. -/
theorem triangle_based_normalization [SimplyConnectedSpace X] (x : X) (tau : Simplex X 2)
    (hv : ∀ i : Fin 3, tau (stdSimplex.vertex i) = x) :
    ∃ g : Simplex X 2, Nonempty (tau.Homotopy g) ∧
      ∀ i : Fin 3, face i g = ContinuousMap.const (Domain 1) x := by
  classical
  have hvertex (i : Fin 3) (j : Fin 2) : face i tau (stdSimplex.vertex j) = x := by
    rw [face_apply, stdSimplex.map_vertex]
    exact hv _
  let G (i : Fin 3) : ContinuousMap.HomotopyRel (face i tau)
      (ContinuousMap.const (Domain 1) x) (simplexBoundary 1) :=
    Classical.choice (singularEdge_nullhomotopic x (face i tau) (hvertex i 0) (hvertex i 1))
  obtain ⟨g, F, hF⟩ := simplex_face_homotopy_extension tau
    (fun i => (G i).toHomotopy.toContinuousMap)
    (relative_face_homotopies_coherent tau (fun _ => ContinuousMap.const (Domain 1) x) G)
    (fun i z => (G i).apply_zero z)
  refine ⟨g, ⟨F⟩, ?_⟩
  intro i
  apply ContinuousMap.ext
  intro z
  change g (stdSimplex.map (SimplexCategory.δ i) z) = x
  rw [← F.apply_one]
  exact (hF i 1 z).trans ((G i).apply_one z)

end FiniteChains.TopologicalSingular
