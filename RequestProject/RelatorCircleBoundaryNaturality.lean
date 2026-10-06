module

public import RequestProject.PresRelatorCircleEmbedding
public import RequestProject.FinitePosetCycleNaturality

@[expose] public section

/-! Literal presentation inclusions preserve the actual boundary-circle
parametrization exactly. No independent choice of circle coordinates is
made on the larger presentation. Pending Lean verification. -/

noncomputable section
namespace FiniteChains.PresModel.PresWordEmbedding
open Comb

variable {A B J K : Type} {w : J → List (A × Bool)} {v : K → List (B × Bool)}
  (h : PresWordEmbedding w v)

theorem relatorCircleSize_eq (j : J) :
    relatorCircleSize w j = relatorCircleSize v (h.cell j) := by
  simp only [relatorCircleSize, h.word_length]

theorem relatorCircleEnumeration_natural (j : J)
    (hw : 0 < (w j).length) (hv : 0 < (v (h.cell j)).length)
    (i : Fin (relatorCircleSize w j + 2)) :
    h.relatorCircleMap j (relatorCircleEnumeration w j hw i) =
      relatorCircleEnumeration v (h.cell j) hv
        (Fin.cast (congrArg (fun n => n + 2) (h.relatorCircleSize_eq j)) i) := by
  apply (relatorCircleIndexEquiv v (h.cell j)).injective
  apply Fin.ext
  rw [h.relatorCircleMap_index, relatorCircleEnumeration_index,
    relatorCircleEnumeration_index]
  rfl

/-- The actual boundary coordinates of every retained cell commute with
the literal presentation inclusion. -/
theorem relatorCircleBoundaryHomeomorph_natural (j : J)
    (hw : 0 < (w j).length) (hv : 0 < (v (h.cell j)).length)
    (x : orderNerveRealization (RelatorCircle w j)) :
    relatorCircleBoundaryHomeomorph v (h.cell j) hv
      (h.relatorCircleRealizationMap j x) =
        relatorCircleBoundaryHomeomorph w j hw x := by
  exact (relatorCircleCycle w j hw).boundaryHomeomorph_natural_cast
    (relatorCircleCycle v (h.cell j) hv) (h.relatorCircleSize_eq j)
    (h.relatorCircleMap j) (h.relatorCircleMap j).monotone
    (h.relatorCircleEnumeration_natural j hw hv) x

theorem relatorCircleBoundaryHomeomorph_symm_natural (j : J)
    (hw : 0 < (w j).length) (hv : 0 < (v (h.cell j)).length)
    (z : FiniteChains.RelativeAttachment.UnitBoundary (Fin 2 → ℝ)) :
    h.relatorCircleRealizationMap j ((relatorCircleBoundaryHomeomorph w j hw).symm z) =
      (relatorCircleBoundaryHomeomorph v (h.cell j) hv).symm z := by
  apply (relatorCircleBoundaryHomeomorph v (h.cell j) hv).injective
  rw [h.relatorCircleBoundaryHomeomorph_natural j hw hv, Homeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply]

end FiniteChains.PresModel.PresWordEmbedding
