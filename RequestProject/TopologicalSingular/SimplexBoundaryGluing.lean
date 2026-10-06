module

public import RequestProject.TopologicalSingular.SimplexHomotopyExtension
public import RequestProject.TopologicalSingular.TriangleSquareGeometry

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ}

theorem simplex_face_coordinate_zero (i : Fin (n + 2)) (z : Domain n) :
    (stdSimplex.map (SimplexCategory.δ i) z).val i = 0 := by
  change (FunOnFinite.linearMap ℝ ℝ i.succAbove z.val) i = 0
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Fin.succAbove_ne]

noncomputable def simplexFaceBoundary (i : Fin (n + 2)) : C(Domain n, simplexBoundary (n + 1)) where
  toFun z := ⟨stdSimplex.map (SimplexCategory.δ i) z, ⟨i, simplex_face_coordinate_zero i z⟩⟩
  continuous_toFun := (stdSimplex.continuous_map _).subtype_mk _

noncomputable def simplexBoundaryPrismCover (n : ℕ) :
    C((Σ _ : Fin (n + 2), I × Domain n), I × simplexBoundary (n + 1)) where
  toFun w := (w.2.1, simplexFaceBoundary w.1 w.2.2)
  continuous_toFun := continuous_sigma fun i =>
    continuous_fst.prodMk ((simplexFaceBoundary i).continuous.comp continuous_snd)

theorem simplexBoundaryPrismCover_surjective (n : ℕ) :
    Function.Surjective (simplexBoundaryPrismCover n) := by
  rintro ⟨t, z⟩
  obtain ⟨i, hi⟩ := z.property
  obtain ⟨w, hw⟩ := domain_zero_coordinate_face z.val i hi
  refine ⟨⟨i, t, w⟩, ?_⟩
  apply Prod.ext
  · rfl
  · exact Subtype.ext hw

/-- A coherent family of homotopies on the faces glues continuously over
the entire boundary. The target need not be Hausdorff. -/
theorem simplex_boundary_glue (H : Fin (n + 2) → C(I × Domain n, X))
    (hH : ∀ (i j : Fin (n + 2)) (t : I) (z w : Domain n),
      stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w →
        H i (t, z) = H j (t, w)) :
    ∃ F : C(I × simplexBoundary (n + 1), X),
      ∀ (i : Fin (n + 2)) (t : I) (z : Domain n), F (t, simplexFaceBoundary i z) = H i (t, z) := by
  classical
  let q := simplexBoundaryPrismCover n
  have hq : Function.Surjective q := simplexBoundaryPrismCover_surjective n
  obtain ⟨r, hr⟩ := hq.hasRightInverse
  let F : I × simplexBoundary (n + 1) → X := fun w => H (r w).1 (r w).2
  have he : ∀ w : (Σ _ : Fin (n + 2), I × Domain n), F (q w) = H w.1 w.2 := by
    intro w
    have htime := congrArg Prod.fst (hr (q w))
    have hpoint := congrArg (fun v : I × simplexBoundary (n + 1) => v.2.val) (hr (q w))
    change (r (q w)).2.1 = w.2.1 at htime
    change stdSimplex.map (SimplexCategory.δ (r (q w)).1) (r (q w)).2.2 =
      stdSimplex.map (SimplexCategory.δ w.1) w.2.2 at hpoint
    change H (r (q w)).1 ((r (q w)).2.1, (r (q w)).2.2) = H w.1 (w.2.1, w.2.2)
    rw [htime]
    exact hH _ _ _ _ _ hpoint
  have hc : Continuous F := by
    apply (Topology.IsQuotientMap.of_surjective_continuous hq q.continuous).continuous_iff.mpr
    have h : Continuous (fun w : (Σ _ : Fin (n + 2), I × Domain n) => H w.1 w.2) :=
      continuous_sigma (fun i : Fin (n + 2) => (H i).continuous)
    convert h using 1
    funext w
    exact he w
  exact ⟨⟨F, hc⟩, fun i t z => he ⟨i, t, z⟩⟩

/-- Simultaneously extend prescribed homotopies on all faces of a simplex. -/
theorem simplex_face_homotopy_extension (f : C(Domain (n + 1), X))
    (H : Fin (n + 2) → C(I × Domain n, X))
    (hH : ∀ (i j : Fin (n + 2)) (t : I) (z w : Domain n),
      stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w →
        H i (t, z) = H j (t, w))
    (h0 : ∀ (i : Fin (n + 2)) (z : Domain n), H i (0, z) = face i f z) :
    ∃ g : C(Domain (n + 1), X), ∃ F : f.Homotopy g,
      ∀ (i : Fin (n + 2)) (t : I) (z : Domain n),
        F (t, stdSimplex.map (SimplexCategory.δ i) z) = H i (t, z) := by
  obtain ⟨B, hB⟩ := simplex_boundary_glue H hH
  have hz : ∀ z : simplexBoundary (n + 1), B (0, z) = f z := by
    intro z
    obtain ⟨i, hi⟩ := z.property
    obtain ⟨w, hw⟩ := domain_zero_coordinate_face z.val i hi
    have he : simplexFaceBoundary i w = z := Subtype.ext hw
    rw [← he, hB, h0]
    rfl
  obtain ⟨g, F, hF⟩ := simplex_homotopy_extension f B hz
  refine ⟨g, F, ?_⟩
  intro i t z
  exact (hF t (simplexFaceBoundary i z)).trans (hB i t z)

end FiniteChains.TopologicalSingular
