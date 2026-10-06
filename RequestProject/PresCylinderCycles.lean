module

public import RequestProject.PresPosetDimension
public import RequestProject.OrderComparableCycleHomotopy

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u}

theorem rose_strict_triangles_empty : IsEmpty (StrictOrdTri (Rose α)) := by
  refine ⟨fun t => ?_⟩
  have h01 := roseDimension_strictMono t.2.1
  have h12 := roseDimension_strictMono t.2.2
  have hlo : 1 ≤ roseDimension t.1.1 := by cases t.1.1 <;> simp [roseDimension]
  have hhi : roseDimension t.1.2.2 ≤ 2 := by cases t.1.2.2 <;> simp [roseDimension]
  omega

theorem cylinder_strict_three_flags_empty (w : J → List (α × Bool)) :
    IsEmpty (StrictOrdTet (CylBase w)) := by
  refine ⟨fun t => ?_⟩
  have h01 := cylinderDimension_strictMono w t.2.1
  have h12 := cylinderDimension_strictMono w t.2.2.1
  have h23 := cylinderDimension_strictMono w t.2.2.2
  have hb := presPosDimension_le_two w (ConeAdj.inc (S := circSet w) t.1.2.2.2)
  change cylinderDimension w t.1.2.2.2 ≤ 2 at hb
  omega

theorem cylinder_normalized_collapse_triangle_zero (w : J → List (α × Bool))
    (t : OrdTri (CylBase w)) :
    normalizeOrdTriangle
      ((orderCxMap (cylCollapse (aHom w)) (cylCollapse_monotone (aHom w))).onF t) = 0 := by
  classical
  unfold normalizeOrdTriangle
  split
  · rename_i h
    haveI := rose_strict_triangles_empty (α := α)
    have tr : StrictOrdTri (Rose α) :=
      ⟨(cylRetr (aHom w) t.1.1, cylRetr (aHom w) t.1.2.1,
        cylRetr (aHom w) t.1.2.2), h⟩
    exact isEmptyElim tr
  · rfl

theorem cylinder_normalized_collapse_zero (w : J → List (α × Bool))
    (c : StrictOrdTri (CylBase w) →₀ ℤ) :
    normalizedStrictChain2 (cylCollapse (aHom w)) (cylCollapse_monotone (aHom w)) c = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add c d hc hd => rw [map_add, hc, hd, add_zero]
  | single t n =>
    rw [normalizedStrictChain2_single, cylinder_normalized_collapse_triangle_zero, smul_zero]

/-- The actual presentation mapping cylinder contributes no strict two-cycles. -/
theorem cylinder_two_cycle_zero (w : J → List (α × Bool))
    (c : StrictOrdTri (CylBase w) →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx (CylBase w)) c = 0) : c = 0 := by
  obtain ⟨y, hy⟩ := strict_cycle_comparable_boundary id (cylCollapse (aHom w))
    monotone_id (cylCollapse_monotone (aHom w)) (le_cylIn_cylRetr (aHom w)) c hc
  haveI := cylinder_strict_three_flags_empty w
  have hy0 : y = 0 := by
    ext t
    exact isEmptyElim t
  rw [hy0, map_zero, cylinder_normalized_collapse_zero, normalizedStrictChain2_id,
    zero_sub] at hy
  exact neg_eq_zero.mp hy.symm

end FiniteChains.PresModel
