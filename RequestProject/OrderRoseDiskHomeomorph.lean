import RequestProject.OrderRoseWedgeTopology
import RequestProject.ClassicalGraphRose

/-! A once-traversed four-vertex order circle gives the exact disk-graph
realization of an arbitrary rose. Continuity of the inverse uses the genuine
weak topology, so the generator set may be infinite. -/

noncomputable section
namespace FiniteChains.PresModel
open Comb RelativeAttachment ClassicalGraphModel Topology
open scoped Classical unitInterval

variable (α : Type)
    (L : Path (orderRoseBase PUnit) (orderRoseBase PUnit))
    (hsur : Function.Surjective L)
    (hfiber : ∀ s t : I, L s = L t →
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0))

private def roseDiskLoopMap : C(DiskFamily α (Fin 1 → ℝ),
    orderNerveRealization (Rose α)) where
  toFun d := roseCopyRealization d.1 (L (graphDiskHomeomorph.symm d.2))
  continuous_toFun := continuous_sigma (fun a =>
    (roseCopyRealization a).continuous.comp (L.continuous.comp graphDiskHomeomorph.symm.continuous))

def diskRoseToOrderRose : C(ClassicalGraphModel.Rose α, orderNerveRealization (Rose α)) :=
  desc (roseAttaching α) (boundaryFamilyInclusion α (Fin 1 → ℝ))
    (ContinuousMap.const _ (orderRoseBase α)) (roseDiskLoopMap α L) (by
      rintro ⟨a, b⟩
      rcases graphBoundary_cases b with rfl | rfl
      · change orderRoseBase α = roseCopyRealization a
          (L (graphDiskHomeomorph.symm (unitBoundaryInclusion _ graphBoundaryNeg)))
        rw [graphDiskHomeomorph_symm_neg, L.source, roseCopyRealization_base]
      · change orderRoseBase α = roseCopyRealization a
          (L (graphDiskHomeomorph.symm (unitBoundaryInclusion _ graphBoundaryPos)))
        rw [graphDiskHomeomorph_symm_pos, L.target, roseCopyRealization_base])

@[simp] theorem diskRoseToOrderRose_vertex :
    diskRoseToOrderRose α L (roseVertex α) = orderRoseBase α := rfl

@[simp] theorem diskRoseToOrderRose_cell (a : α) (d : ClosedUnitBall (Fin 1 → ℝ)) :
    diskRoseToOrderRose α L (cell (roseAttaching α) (boundaryFamilyInclusion α _) ⟨a, d⟩) =
      roseCopyRealization a (L (graphDiskHomeomorph.symm d)) := desc_cell ..

theorem diskRoseToOrderRose_interval (a : α) (t : I) :
    diskRoseToOrderRose α L
      (cell (roseAttaching α) (boundaryFamilyInclusion α _) ⟨a, graphDiskHomeomorph t⟩) =
      roseCopyRealization a (L t) := by
  rw [diskRoseToOrderRose_cell, Homeomorph.symm_apply_apply]

private theorem freshParameter_ne_endpoints
    (d : {d : DiskFamily α (Fin 1 → ℝ) // d ∉ Set.range (boundaryFamilyInclusion α _)}) :
    graphDiskHomeomorph.symm d.val.2 ≠ 0 ∧ graphDiskHomeomorph.symm d.val.2 ≠ 1 := by
  constructor
  · intro ht
    apply d.property
    refine ⟨⟨d.val.1, graphBoundaryNeg⟩, ?_⟩
    change Sigma.mk d.val.1 (unitBoundaryInclusion _ graphBoundaryNeg) = d.val
    cases d with
    | mk d hd =>
      cases d with
      | mk a x =>
        dsimp at ht ⊢
        apply congrArg (Sigma.mk a)
        rw [← graphDiskHomeomorph_zero, ← ht, Homeomorph.apply_symm_apply]
  · intro ht
    apply d.property
    refine ⟨⟨d.val.1, graphBoundaryPos⟩, ?_⟩
    change Sigma.mk d.val.1 (unitBoundaryInclusion _ graphBoundaryPos) = d.val
    cases d with
    | mk d hd =>
      cases d with
      | mk a x =>
        dsimp at ht ⊢
        apply congrArg (Sigma.mk a)
        rw [← graphDiskHomeomorph_one, ← ht, Homeomorph.apply_symm_apply]

include hfiber in
private theorem traversal_eq_base {t : I} (h : L t = orderRoseBase PUnit) : t = 0 ∨ t = 1 := by
  rcases hfiber t 0 (h.trans L.source.symm) with ht | ht | ht
  · exact Or.inl ht
  · exact Or.inl ht.1
  · exact Or.inr ht.1

include hfiber in
private theorem freshImage_ne_base
    (d : {d : DiskFamily α (Fin 1 → ℝ) // d ∉ Set.range (boundaryFamilyInclusion α _)}) :
    roseCopyRealization d.val.1 (L (graphDiskHomeomorph.symm d.val.2)) ≠ orderRoseBase α := by
  intro h
  have he : L (graphDiskHomeomorph.symm d.val.2) = orderRoseBase PUnit :=
    roseCopyRealization_injective d.val.1 (h.trans (roseCopyRealization_base d.val.1).symm)
  exact (traversal_eq_base L hfiber he).elim
    (freshParameter_ne_endpoints α d).1 (freshParameter_ne_endpoints α d).2

private theorem diskRoseToOrderRose_fresh
    (d : {d : DiskFamily α (Fin 1 → ℝ) // d ∉ Set.range (boundaryFamilyInclusion α _)}) :
    diskRoseToOrderRose α L (Sum.inr d) =
      roseCopyRealization d.val.1 (L (graphDiskHomeomorph.symm d.val.2)) := by
  rw [← cell_of_not_mem (roseAttaching α) _ d.val d.property]
  exact diskRoseToOrderRose_cell α L d.val.1 d.val.2

include hsur hfiber in
theorem diskRoseToOrderRose_bijective : Function.Bijective (diskRoseToOrderRose α L) := by
  constructor
  · intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subsingleton.elim x y)
      | inr y =>
        have hy : diskRoseToOrderRose α L (Sum.inl x) = orderRoseBase α := rfl
        rw [hy, diskRoseToOrderRose_fresh] at h
        exact (freshImage_ne_base α L hfiber y h.symm).elim
    | inr x =>
      cases y with
      | inl y =>
        have hy : diskRoseToOrderRose α L (Sum.inl y) = orderRoseBase α := rfl
        rw [hy, diskRoseToOrderRose_fresh] at h
        exact (freshImage_ne_base α L hfiber x h).elim
      | inr y =>
        rw [diskRoseToOrderRose_fresh, diskRoseToOrderRose_fresh] at h
        by_cases ha : x.val.1 = y.val.1
        · rw [← ha] at h
          have ht := roseCopyRealization_injective x.val.1 h
          rcases hfiber _ _ ht with ht | ht | ht
          · apply congrArg Sum.inr
            apply Subtype.ext
            exact Sigma.ext ha (heq_of_eq (graphDiskHomeomorph.symm.injective ht))
          · exact ((freshParameter_ne_endpoints α x).1 ht.1).elim
          · exact ((freshParameter_ne_endpoints α x).2 ht.1).elim
        · have hx := (roseCopyRealization_intersection ha _ _ h).1
          exact ((traversal_eq_base L hfiber hx).elim
            (freshParameter_ne_endpoints α x).1 (freshParameter_ne_endpoints α x).2).elim
  · intro x
    rcases orderRoseRealization_cases x with rfl | ⟨a, u, rfl⟩
    · exact ⟨roseVertex α, diskRoseToOrderRose_vertex α L⟩
    · obtain ⟨t, rfl⟩ := hsur u
      exact ⟨cell (roseAttaching α) (boundaryFamilyInclusion α _) ⟨a, graphDiskHomeomorph t⟩,
        diskRoseToOrderRose_interval α L a t⟩

def diskRoseOrderHomeomorphOfTraversal :
    ClassicalGraphModel.Rose α ≃ₜ orderNerveRealization (Rose α) := by
  let e := Equiv.ofBijective (diskRoseToOrderRose α L)
    (diskRoseToOrderRose_bijective α L hsur hfiber)
  refine { toEquiv := e
           continuous_toFun := (diskRoseToOrderRose α L).continuous
           continuous_invFun := ?_ }
  apply (orderRoseRealization_continuous_iff e.symm).mpr
  intro a
  have hq : IsQuotientMap L := L.continuous.isClosedMap.isQuotientMap L.continuous hsur
  apply hq.continuous_iff.mpr
  have he : (e.symm ∘ roseCopyRealization a) ∘ L =
      fun t => cell (roseAttaching α) (boundaryFamilyInclusion α _) ⟨a, graphDiskHomeomorph t⟩ := by
    funext t
    apply e.injective
    dsimp only [Function.comp_apply]
    rw [e.apply_symm_apply]
    exact (diskRoseToOrderRose_interval α L a t).symm
  rw [he]
  exact (cell_continuous (roseAttaching α) _).comp
    ((continuous_sigmaMk («σ» := fun _ : α => ClosedUnitBall (Fin 1 → ℝ)) (i := a)).comp
      graphDiskHomeomorph.continuous)

theorem diskRoseOrderHomeomorphOfTraversal_interval (a : α) (t : I) :
    diskRoseOrderHomeomorphOfTraversal α L hsur hfiber
      (cell (roseAttaching α) (boundaryFamilyInclusion α _) ⟨a, graphDiskHomeomorph t⟩) =
      roseCopyRealization a (L t) := diskRoseToOrderRose_interval α L a t

@[simp] theorem diskRoseOrderHomeomorphOfTraversal_vertex :
    diskRoseOrderHomeomorphOfTraversal α L hsur hfiber (roseVertex α) = orderRoseBase α := rfl

end FiniteChains.PresModel
