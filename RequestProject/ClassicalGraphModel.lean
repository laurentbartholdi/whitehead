import RequestProject.ClassicalCellAttachmentMaps
import RequestProject.SpanningTree
import Mathlib.Topology.Path

/-! The literal one-dimensional disk attachment and its oriented graph.
The interval parametrization uses the original sup-norm characteristic disks. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
open scoped unitInterval Topology Classical

theorem finOne_norm (x : Fin 1 → ℝ) : ‖x‖ = |x 0| := by
  have hx : x = fun _ => x 0 := funext fun i => congrArg x (Subsingleton.elim i 0)
  calc
    ‖x‖ = ‖fun _ : Fin 1 => x 0‖ := congrArg norm hx
    _ = |x 0| := by rw [pi_norm_const, Real.norm_eq_abs]

def graphBoundaryNeg : UnitBoundary (Fin 1 → ℝ) :=
  ⟨fun _ => -1, by simp [pi_norm_const]⟩

def graphBoundaryPos : UnitBoundary (Fin 1 → ℝ) :=
  ⟨fun _ => 1, by simp [pi_norm_const]⟩

theorem graphBoundary_cases (a : UnitBoundary (Fin 1 → ℝ)) :
    a = graphBoundaryNeg ∨ a = graphBoundaryPos := by
  have ha : |a.val 0| = 1 := (finOne_norm a.val).symm.trans a.property
  by_cases h : 0 ≤ a.val 0
  · right
    apply Subtype.ext
    funext i
    rw [show i = 0 from Subsingleton.elim _ _]
    simpa [graphBoundaryNeg, graphBoundaryPos,abs_of_nonneg h] using ha
  · left
    have hn : a.val 0 = -1 := by
      rw [abs_of_neg (lt_of_not_ge h)] at ha
      linarith
    apply Subtype.ext
    funext i
    rw [show i = 0 from Subsingleton.elim _ _]
    exact hn

def graphDiskHomeomorph : I ≃ₜ ClosedUnitBall (Fin 1 → ℝ) where
  toFun s := ⟨fun _ => 2 * (s : ℝ) - 1, by
    rw [pi_norm_const, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [s.property.1], by linarith [s.property.2]⟩⟩
  invFun d := ⟨(d.val 0 + 1) / 2, by
    have hd : |d.val 0| ≤ 1 := by simpa only [finOne_norm] using d.property
    obtain ⟨hl, hu⟩ := abs_le.mp hd
    constructor <;> linarith⟩
  left_inv s := by
    apply Subtype.ext
    dsimp
    ring
  right_inv d := by
    apply Subtype.ext
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    dsimp
    ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun _ =>
      (continuous_const.mul continuous_subtype_val).sub continuous_const
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (((continuous_apply 0).comp continuous_subtype_val).add continuous_const).div_const 2

@[simp] theorem graphDiskHomeomorph_zero :
    graphDiskHomeomorph 0 = unitBoundaryInclusion (Fin 1 → ℝ) graphBoundaryNeg := by
  apply Subtype.ext
  funext i
  norm_num [graphDiskHomeomorph, graphBoundaryNeg, unitBoundaryInclusion]

@[simp] theorem graphDiskHomeomorph_one :
    graphDiskHomeomorph 1 = unitBoundaryInclusion (Fin 1 → ℝ) graphBoundaryPos := by
  apply Subtype.ext
  funext i
  norm_num [graphDiskHomeomorph, graphBoundaryPos, unitBoundaryInclusion]

@[simp] theorem graphDiskHomeomorph_symm_neg :
    graphDiskHomeomorph.symm (unitBoundaryInclusion (Fin 1 → ℝ) graphBoundaryNeg) = 0 := by
  rw [← graphDiskHomeomorph_zero, graphDiskHomeomorph.symm_apply_apply]

@[simp] theorem graphDiskHomeomorph_symm_pos :
    graphDiskHomeomorph.symm (unitBoundaryInclusion (Fin 1 → ℝ) graphBoundaryPos) = 1 := by
  rw [← graphDiskHomeomorph_one, graphDiskHomeomorph.symm_apply_apply]

variable {V J : Type} [TopologicalSpace V]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V)

def graphSrc (j : J) : V := r ⟨j, graphBoundaryNeg⟩
def graphTgt (j : J) : V := r ⟨j, graphBoundaryPos⟩

def graphCx : Comb.Complex2 where
  V := V
  E := J
  F := Empty
  src := graphSrc r
  tgt := graphTgt r
  base := Empty.elim
  att := Empty.elim
  att_isLoop f := Empty.elim f

def graphEdgePath (j : J) :
    Path (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) (graphSrc r j))
      (old r (boundaryFamilyInclusion J (Fin 1 → ℝ)) (graphTgt r j)) where
  toFun s := cell r (boundaryFamilyInclusion J (Fin 1 → ℝ)) ⟨j, graphDiskHomeomorph s⟩
  continuous_toFun := (cell_continuous r _).comp
    (continuous_sigmaMk.comp graphDiskHomeomorph.continuous)
  source' := by
    rw [graphDiskHomeomorph_zero]
    exact cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J _).injective
      ⟨j, graphBoundaryNeg⟩
  target' := by
    rw [graphDiskHomeomorph_one]
    exact cell_boundary r _ (boundaryFamilyInclusion_isClosedEmbedding J _).injective
      ⟨j, graphBoundaryPos⟩

def graphGermPath (g : J × Bool) :
    Path (old r (boundaryFamilyInclusion J (Fin 1 → ℝ))
      (Comb.germSrc (graphSrc r) (graphTgt r) g))
      (old r (boundaryFamilyInclusion J (Fin 1 → ℝ))
        (Comb.germTgt (graphSrc r) (graphTgt r) g)) := by
  rcases g with ⟨j, b⟩
  cases b
  · exact (graphEdgePath r j).symm
  · exact graphEdgePath r j

end FiniteChains.ClassicalGraphModel
