import RequestProject.HomeomorphContinuousMap
import RequestProject.DiskFamilyHomotopyBaseChange
import RequestProject.DiskFamilyMap
import RequestProject.AttachingHomotopyChosenExtensions

/-! Explicit disk extensions, natural in the base map and disk labels.
The extension on a disk is the fixed ball-cylinder retraction, independent
of other cells or the stage containing it. Unverified source. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open scoped Classical Topology unitInterval
variable {J K E X Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [TopologicalSpace Y]

theorem ballHomotopyExtension_natural
    (f : C(X, Y)) (d : C(ClosedUnitBall E, X)) (d' : C(ClosedUnitBall E, Y))
    (H : C(I × UnitBoundary E, X)) (H' : C(I × UnitBoundary E, Y))
    (h₀ : ∀ a, H (0, a) = d (unitBoundaryInclusion E a))
    (h₀' : ∀ a, H' (0, a) = d' (unitBoundaryInclusion E a))
    (hd : ∀ x, f (d x) = d' x) (hH : ∀ t a, f (H (t, a)) = H' (t, a))
    (t : I) (x : ClosedUnitBall E) :
    f (ballHomotopyExtension d H h₀ (t, x)) =
      ballHomotopyExtension d' H' h₀' (t, x) := by
  let z := ballCylinderRetraction (t, x)
  change f (if hz : z.val.1 = 0 then d z.val.2 else
      H (z.val.1, ⟨z.val.2.val, z.property.resolve_left hz⟩)) =
    if hz : z.val.1 = 0 then d' z.val.2 else
      H' (z.val.1, ⟨z.val.2.val, z.property.resolve_left hz⟩)
  split_ifs with hz
  · exact hd _
  · exact hH _ _

variable (r₀ r₁ : C(BoundaryFamily J E, X)) (H : r₀.Homotopy r₁)

omit [NormedSpace ℝ E] in
theorem naturalDiskBoundaryStart (j : J) (a : UnitBoundary E) :
    old r₀ (boundaryFamilyInclusion J E) (H (0, ⟨j, a⟩)) =
      cell r₀ (boundaryFamilyInclusion J E) ⟨j, unitBoundaryInclusion E a⟩ := by
  rw [H.apply_zero]
  exact (cell_boundary r₀ _ (boundaryFamilyInclusion_isClosedEmbedding J E).injective
    ⟨j, a⟩).symm

def naturalDiskExtensionAt (j : J) : C(I × ClosedUnitBall E, DiskAttachment r₀) :=
  ballHomotopyExtension
    ⟨fun x => cell r₀ (boundaryFamilyInclusion J E) ⟨j, x⟩,
      (cell_continuous _ _).comp
        (continuous_sigmaMk («σ» := fun _ : J => ClosedUnitBall E) (i := j))⟩
    ⟨fun ta => old r₀ (boundaryFamilyInclusion J E) (H (ta.1, ⟨j, ta.2⟩)),
      (old_continuous _ _).comp (H.continuous.comp
        (continuous_fst.prodMk
          ((continuous_sigmaMk («σ» := fun _ : J => UnitBoundary E) (i := j)).comp
            continuous_snd)))⟩
    (naturalDiskBoundaryStart r₀ r₁ H j)

def naturalDiskExtension : C(I × DiskFamily J E, DiskAttachment r₀) :=
  (⟨fun z : Σ _ : J, I × ClosedUnitBall E => naturalDiskExtensionAt r₀ r₁ H z.1 z.2,
    continuous_sigma (fun j => (naturalDiskExtensionAt r₀ r₁ H j).continuous)⟩ :
      C((Σ _ : J, I × ClosedUnitBall E), DiskAttachment r₀)).comp
    (sigmaCylinderHomeomorph (D := fun _ : J => ClosedUnitBall E)).symm.toContinuousMap

theorem naturalDiskExtension_zero (d : DiskFamily J E) :
    naturalDiskExtension r₀ r₁ H (0, d) = cell r₀ (boundaryFamilyInclusion J E) d := by
  change naturalDiskExtensionAt r₀ r₁ H d.1 (0, d.2) = _
  unfold naturalDiskExtensionAt
  rw [ballHomotopyExtension_zero]
  rfl

theorem naturalDiskExtension_boundary (t : I) (a : BoundaryFamily J E) :
    naturalDiskExtension r₀ r₁ H (t, boundaryFamilyInclusion J E a) =
      old r₀ (boundaryFamilyInclusion J E) (H (t, a)) := by
  change naturalDiskExtensionAt r₀ r₁ H a.1 (t, unitBoundaryInclusion E a.2) = _
  unfold naturalDiskExtensionAt
  rw [ballHomotopyExtension_boundary]
  rfl

def naturalDiskBackward : C(DiskAttachment r₁, DiskAttachment r₀) :=
  desc r₁ (boundaryFamilyInclusion J E)
    ⟨old r₀ (boundaryFamilyInclusion J E), old_continuous _ _⟩
    ((naturalDiskExtension r₀ r₁ H).comp
      ⟨fun d => (1, d), continuous_const.prodMk continuous_id⟩)
    (fun a => by
      change old r₀ (boundaryFamilyInclusion J E) (r₁ a) =
        naturalDiskExtension r₀ r₁ H (1, boundaryFamilyInclusion J E a)
      rw [naturalDiskExtension_boundary, H.apply_one])

@[simp] theorem naturalDiskBackward_old (x : X) :
    naturalDiskBackward r₀ r₁ H (old r₁ (boundaryFamilyInclusion J E) x) =
      old r₀ (boundaryFamilyInclusion J E) x := rfl

@[simp] theorem naturalDiskBackward_cell (d : DiskFamily J E) :
    naturalDiskBackward r₀ r₁ H (cell r₁ (boundaryFamilyInclusion J E) d) =
      naturalDiskExtension r₀ r₁ H (1, d) := by
  unfold naturalDiskBackward
  rw [desc_cell]
  rfl

variable (s₀ s₁ : C(BoundaryFamily K E, Y)) (G : s₀.Homotopy s₁)
  (f : C(X, Y)) (i : J → K)
  (h₀ : ∀ j a, f (r₀ ⟨j, a⟩) = s₀ ⟨i j, a⟩)
  (h₁ : ∀ j a, f (r₁ ⟨j, a⟩) = s₁ ⟨i j, a⟩)
  (hH : ∀ t j a, f (H (t, ⟨j, a⟩)) = G (t, ⟨i j, a⟩))

include hH in
theorem naturalDiskExtension_natural (t : I) (j : J) (x : ClosedUnitBall E) :
    diskFamilyMap r₀ s₀ f i h₀ (naturalDiskExtension r₀ r₁ H (t, ⟨j, x⟩)) =
      naturalDiskExtension s₀ s₁ G (t, ⟨i j, x⟩) := by
  apply ballHomotopyExtension_natural (diskFamilyMap r₀ s₀ f i h₀) _ _ _ _
    (naturalDiskBoundaryStart r₀ r₁ H j) (naturalDiskBoundaryStart s₀ s₁ G (i j))
  · intro d
    exact diskFamilyMap_cell r₀ s₀ f i h₀ j d
  · intro τ a
    change diskFamilyMap r₀ s₀ f i h₀
      (old r₀ (boundaryFamilyInclusion J E) (H (τ, ⟨j, a⟩))) =
        old s₀ (boundaryFamilyInclusion K E) (G (τ, ⟨i j, a⟩))
    rw [diskFamilyMap_old, hH]

include hH in
theorem naturalDiskBackward_natural :
    (diskFamilyMap r₀ s₀ f i h₀).comp (naturalDiskBackward r₀ r₁ H) =
      (naturalDiskBackward s₀ s₁ G).comp (diskFamilyMap r₁ s₁ f i h₁) := by
  apply hom_ext r₁ (boundaryFamilyInclusion J E)
  · intro x
    rfl
  · rintro ⟨j, x⟩
    dsimp only [ContinuousMap.comp_apply]
    change diskFamilyMap r₀ s₀ f i h₀ (naturalDiskBackward r₀ r₁ H (cell _ _ ⟨j, x⟩)) = _
    rw [naturalDiskBackward_cell, naturalDiskExtension_natural r₀ r₁ H s₀ s₁ G f i h₀ hH,
      diskFamilyMap_cell, naturalDiskBackward_cell]

end FiniteChains.RelativeAttachment
