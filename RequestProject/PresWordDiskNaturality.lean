import RequestProject.PresClassicalDiskComparison
import RequestProject.RelatorCircleBoundaryNaturality
import RequestProject.DiskRoseMaps

/-! The actual attaching maps and disk-model maps commute with literal
presentation-word embeddings. Circle-coordinate compatibility is proved
by the explicit traversal, rather than supplied as an extra hypothesis. -/

noncomputable section
namespace FiniteChains.PresModel.PresWordEmbedding
open Comb RelativeAttachment ClassicalGraphModel
open scoped Topology

variable {A B J K : Type} {w : J → List (A × Bool)} {v : K → List (B × Bool)}
  (h : PresWordEmbedding w v) (hw : ∀ j, w j ≠ []) (hv : ∀ k, v k ≠ [])

theorem actualPresWordAttaching_natural (z : BoundaryFamily J (Fin 2 → ℝ)) :
    orderNerveRealizationMap h.roseMap h.roseMap.monotone (actualPresWordAttaching w hw z) =
      actualPresWordAttaching v hv ⟨h.cell z.1, z.2⟩ := by
  rcases z with ⟨j, a⟩
  rw [actualPresWordAttaching_apply, actualPresWordAttaching_apply]
  have hs := h.relatorCircleBoundaryHomeomorph_symm_natural j
    (List.length_pos_of_ne_nil (hw j)) (List.length_pos_of_ne_nil (hv (h.cell j))) a
  change h.relatorCircleRealizationMap j ((presCircleBoundaryHomeomorph w hw j).symm a) =
    (presCircleBoundaryHomeomorph v hv (h.cell j)).symm a at hs
  rw [← hs]
  exact h.presCircleWordMap_natural j _

theorem classicalPresWordAttaching_natural (z : BoundaryFamily J (Fin 2 → ℝ)) :
    diskRoseMap h.gen (classicalPresWordAttaching w hw z) =
      classicalPresWordAttaching v hv ⟨h.cell z.1, z.2⟩ := by
  change diskRoseMap h.gen (orderRoseRealizationHomeomorph A (actualPresWordAttaching w hw z)) =
    orderRoseRealizationHomeomorph B (actualPresWordAttaching v hv ⟨h.cell z.1, z.2⟩)
  rw [← orderRoseRealizationHomeomorph_natural h, h.actualPresWordAttaching_natural hw hv z]

def orderRoseMapContinuous : C(orderNerveRealization (PresModel.Rose A),
    orderNerveRealization (PresModel.Rose B)) :=
  (orderNerveRealizationMap h.roseMap h.roseMap.monotone).hom

def wordDiskCellMap : C(DiskFamily J (Fin 2 → ℝ), ActualPresWordDisks v hv) :=
  (⟨RelativeAttachment.cell (actualPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ)),
    cell_continuous _ _⟩ : C(DiskFamily K (Fin 2 → ℝ), _)).comp
      ⟨fun d => ⟨h.cell d.1, d.2⟩, continuous_sigma (fun j => continuous_sigmaMk
          (σ := fun _ : K => ClosedUnitBall (Fin 2 → ℝ)) (i := h.cell j))⟩

def wordDiskMap : C(ActualPresWordDisks w hw, ActualPresWordDisks v hv) :=
  desc (actualPresWordAttaching w hw) (boundaryFamilyInclusion J (Fin 2 → ℝ))
    ((⟨old (actualPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ)),
      old_continuous _ _⟩ : C(orderNerveRealization (PresModel.Rose B), _)).comp
        h.orderRoseMapContinuous)
    (h.wordDiskCellMap hv)
    (fun a => by
      change old (actualPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ))
        (orderNerveRealizationMap h.roseMap h.roseMap.monotone
        (actualPresWordAttaching w hw a)) =
          RelativeAttachment.cell _ _ (boundaryFamilyInclusion K (Fin 2 → ℝ) ⟨h.cell a.1, a.2⟩)
      rw [cell_boundary _ _ (boundaryFamilyInclusion_isClosedEmbedding K (Fin 2 → ℝ)).injective,
        h.actualPresWordAttaching_natural hw hv])

@[simp] theorem wordDiskMap_old (x : orderNerveRealization (PresModel.Rose A)) :
    h.wordDiskMap hw hv (old (actualPresWordAttaching w hw) (boundaryFamilyInclusion J (Fin 2 → ℝ)) x) =
      old (actualPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ))
        (orderNerveRealizationMap h.roseMap h.roseMap.monotone x) := rfl

@[simp] theorem wordDiskMap_cell (d : DiskFamily J (Fin 2 → ℝ)) :
    h.wordDiskMap hw hv (RelativeAttachment.cell (actualPresWordAttaching w hw) (boundaryFamilyInclusion J (Fin 2 → ℝ)) d) =
      RelativeAttachment.cell (actualPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ))
        ⟨h.cell d.1, d.2⟩ := desc_cell ..

def classicalWordDiskMap : C(ClassicalPresWordDisks w hw, ClassicalPresWordDisks v hv) :=
  desc (classicalPresWordAttaching w hw) (boundaryFamilyInclusion J (Fin 2 → ℝ))
    ((⟨old (classicalPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ)),
      old_continuous _ _⟩ : C(ClassicalGraphModel.Rose B, _)).comp (diskRoseMap h.gen))
    ((⟨RelativeAttachment.cell (classicalPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ)),
      cell_continuous _ _⟩ : C(DiskFamily K (Fin 2 → ℝ), _)).comp
        ⟨fun d => ⟨h.cell d.1, d.2⟩, continuous_sigma (fun j => continuous_sigmaMk
          (σ := fun _ : K => ClosedUnitBall (Fin 2 → ℝ)) (i := h.cell j))⟩)
    (fun a => by
      change old (classicalPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ))
        (diskRoseMap h.gen (classicalPresWordAttaching w hw a)) =
        RelativeAttachment.cell _ _ (boundaryFamilyInclusion K (Fin 2 → ℝ) ⟨h.cell a.1, a.2⟩)
      rw [cell_boundary _ _ (boundaryFamilyInclusion_isClosedEmbedding K (Fin 2 → ℝ)).injective,
        h.classicalPresWordAttaching_natural hw hv])

@[simp] theorem classicalWordDiskMap_old (x : ClassicalGraphModel.Rose A) :
    h.classicalWordDiskMap hw hv
      (old (classicalPresWordAttaching w hw) (boundaryFamilyInclusion J (Fin 2 → ℝ)) x) =
      old (classicalPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ))
        (diskRoseMap h.gen x) := rfl

@[simp] theorem classicalWordDiskMap_cell (d : DiskFamily J (Fin 2 → ℝ)) :
    h.classicalWordDiskMap hw hv
      (RelativeAttachment.cell (classicalPresWordAttaching w hw) (boundaryFamilyInclusion J (Fin 2 → ℝ)) d) =
      RelativeAttachment.cell (classicalPresWordAttaching v hv) (boundaryFamilyInclusion K (Fin 2 → ℝ))
        ⟨h.cell d.1, d.2⟩ := desc_cell ..

end FiniteChains.PresModel.PresWordEmbedding
