module

public import RequestProject.OrderRoseDiskHomeomorph
public import RequestProject.OrderRoseFourVertices
public import RequestProject.FinitePosetCycleRealization

@[expose] public section

/-! The actual arbitrary order rose is homeomorphic to the actual bouquet
of one-dimensional disks. The four-edge generator orientation is retained. -/

noncomputable section
namespace FiniteChains.PresModel
open Comb RelativeAttachment ClassicalGraphModel
open scoped Classical unitInterval

def roseRank : Rose PUnit → ℕ
  | .base => 0
  | .mid _ => 0
  | .edg _ _ => 1

theorem roseRank_strictMono : StrictMono roseRank := by
  intro p q hpq
  have hn := ne_of_lt hpq
  have hl := hpq.le
  change Rose.le p q at hl
  cases p <;> cases q <;> simp_all [Rose.le, roseRank]

def roseFourCycle : FinitePosetCycle (Rose PUnit) 2 where
  positive := by decide
  vertex := roseFourVertexEquiv
  consecutive i := by
    change Rose.le (roseFourVertex i.castSucc) (roseFourVertex i.succ) ∨
      Rose.le (roseFourVertex i.succ) (roseFourVertex i.castSucc)
    fin_cases i <;> simp [roseFourVertex, Rose.le]
  closing := by
    change Rose.le (roseFourVertex (Fin.last 3)) (roseFourVertex 0) ∨
      Rose.le (roseFourVertex 0) (roseFourVertex (Fin.last 3))
    simp [roseFourVertex, Rose.le]
  edges a b hne hab := by
    obtain ⟨i, rfl⟩ := roseFourVertex_surjective a
    obtain ⟨j, rfl⟩ := roseFourVertex_surjective b
    change Rose.le (roseFourVertex i) (roseFourVertex j) ∨
      Rose.le (roseFourVertex j) (roseFourVertex i) at hab
    fin_cases i <;> fin_cases j <;>
      simp_all [roseFourVertexEquiv, roseFourVertex, Rose.le, Fin.exists_fin_succ]
  height := roseRank
  height_strict := roseRank_strictMono
  height_le p := by cases p <;> simp [roseRank]

def orderRoseTraversal : Path (orderRoseBase PUnit) (orderRoseBase PUnit) :=
  roseFourCycle.traversal

theorem orderRoseTraversal_surjective : Function.Surjective orderRoseTraversal :=
  roseFourCycle.traversal_surjective

theorem orderRoseTraversal_fiber (s t : I) (h : orderRoseTraversal s = orderRoseTraversal t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) :=
  roseFourCycle.traversal_fiber s t h

/-- No extra traversal, injectivity, or topology premise remains in this map. -/
def orderRoseRealizationHomeomorph (α : Type) :
    orderNerveRealization (Rose α) ≃ₜ ClassicalGraphModel.Rose α :=
  (diskRoseOrderHomeomorphOfTraversal α orderRoseTraversal
    orderRoseTraversal_surjective orderRoseTraversal_fiber).symm

@[simp] theorem orderRoseRealizationHomeomorph_base (α : Type) :
    orderRoseRealizationHomeomorph α (orderRoseBase α) = roseVertex α := by
  apply (orderRoseRealizationHomeomorph α).symm.injective
  rw [Homeomorph.symm_apply_apply]
  rfl

theorem orderRoseRealizationHomeomorph_interval {α : Type} (a : α) (t : I) :
    orderRoseRealizationHomeomorph α (roseCopyRealization a (orderRoseTraversal t)) =
      cell (roseAttaching α) (boundaryFamilyInclusion α _) ⟨a, graphDiskHomeomorph t⟩ := by
  apply (orderRoseRealizationHomeomorph α).symm.injective
  rw [Homeomorph.symm_apply_apply]
  exact (diskRoseOrderHomeomorphOfTraversal_interval α orderRoseTraversal
    orderRoseTraversal_surjective orderRoseTraversal_fiber a t).symm

end FiniteChains.PresModel
