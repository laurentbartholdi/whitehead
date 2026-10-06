import RequestProject.ClassicalCellAttachmentMaps

/-! Actual maps of disk attachments induced by a base map and a map of
disk labels. These maps retain the complete characteristic disks. Unverified. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open scoped Classical
variable {J K E X Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [TopologicalSpace Y]
  (r : C(BoundaryFamily J E, X)) (s : C(BoundaryFamily K E, Y))
  (f : C(X, Y)) (i : J → K)
  (h : ∀ j a, f (r ⟨j, a⟩) = s ⟨i j, a⟩)

def diskFamilyMap : C(DiskAttachment r, DiskAttachment s) :=
  desc r (boundaryFamilyInclusion J E)
    ((⟨old s (boundaryFamilyInclusion K E), old_continuous _ _⟩ : C(Y, DiskAttachment s)).comp f)
    ⟨fun d => cell s (boundaryFamilyInclusion K E) ⟨i d.1, d.2⟩,
      (cell_continuous _ _).comp (continuous_sigma (fun j =>
        continuous_sigmaMk (σ := fun _ : K => ClosedUnitBall E) (i := i j)))⟩
    (fun a => by
      change old s (boundaryFamilyInclusion K E) (f (r a)) =
        cell s (boundaryFamilyInclusion K E) ⟨i a.1, unitBoundaryInclusion E a.2⟩
      rw [h]
      exact (cell_boundary s _ (boundaryFamilyInclusion_isClosedEmbedding K E).injective
        ⟨i a.1, a.2⟩).symm)

omit [NormedSpace ℝ E] in
@[simp] theorem diskFamilyMap_old (x : X) :
    diskFamilyMap r s f i h (old r (boundaryFamilyInclusion J E) x) =
      old s (boundaryFamilyInclusion K E) (f x) := rfl

omit [NormedSpace ℝ E] in
@[simp] theorem diskFamilyMap_cell (j : J) (x : ClosedUnitBall E) :
    diskFamilyMap r s f i h (cell r (boundaryFamilyInclusion J E) ⟨j, x⟩) =
      cell s (boundaryFamilyInclusion K E) ⟨i j, x⟩ := by
  unfold diskFamilyMap
  rw [desc_cell]
  rfl

end FiniteChains.RelativeAttachment
