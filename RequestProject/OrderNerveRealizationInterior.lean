module

public import RequestProject.OrderNerveAffineCoordinates
public import Mathlib.Order.WellFounded

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory
open scoped Classical

/-- At a simplex point with positive barycentric coordinates, a vertex indicator
has positive value precisely on the vertices of that simplex. -/
theorem orderNerveAffineSimplex_indicator_pos_iff {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (z : SimplexCategory.toTop.obj n) (hz : ∀ i, 0 < z.down.weights i) (p : P) :
    0 < orderNerveAffineSimplex (fun q => if q = p then 1 else 0) s z ↔
      p ∈ Set.range s.obj := by
  classical
  constructor
  · intro h
    by_contra hp
    have hn : ∀ i, s.obj i ≠ p := fun i hi => hp ⟨i, hi⟩
    simp [orderNerveAffineSimplex, hn] at h
  · rintro ⟨i, rfl⟩
    change 0 < ∑ j, z.down.weights j * (if s.obj j = s.obj i then 1 else 0)
    have hsum := Finset.single_le_sum
      (f := fun j => z.down.weights j * (if s.obj j = s.obj i then 1 else 0))
      (fun j _ => mul_nonneg (le_of_lt (hz j)) (by split_ifs <;> norm_num))
      (Finset.mem_univ i)
    have hi : z.down.weights i ≤ ∑ j, z.down.weights j * (if s.obj j = s.obj i then 1 else 0) := by
      simpa using hsum
    exact (hz i).trans_le hi

/-- Two actual simplex interiors meeting in the realization have the same vertex set. -/
theorem orderNerveRealizationSimplex_interior_range_eq {P : Type} [PartialOrder P]
    {n m : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (t : (nerve P).obj (Opposite.op m))
    (z : SimplexCategory.toTop.obj n) (w : SimplexCategory.toTop.obj m)
    (hz : ∀ i, 0 < z.down.weights i) (hw : ∀ i, 0 < w.down.weights i)
    (h : orderNerveRealizationSimplex P s z = orderNerveRealizationSimplex P t w) :
    Set.range s.obj = Set.range t.obj := by
  ext p
  let v : P → ℝ := fun q => if q = p then 1 else 0
  have hf := congrArg (orderNerveAffineRealization v) h
  have hc := congrArg (fun k => k z) (orderNerveAffineRealization_simplex v s)
  have hd := congrArg (fun k => k w) (orderNerveAffineRealization_simplex v t)
  change orderNerveAffineRealization v (orderNerveRealizationSimplex P s z) =
    orderNerveAffineSimplex v s z at hc
  change orderNerveAffineRealization v (orderNerveRealizationSimplex P t w) =
    orderNerveAffineSimplex v t w at hd
  rw [hc, hd] at hf
  rw [← orderNerveAffineSimplex_indicator_pos_iff s z hz p,
    ← orderNerveAffineSimplex_indicator_pos_iff t w hw p]
  exact congrArg (fun r : ℝ => 0 < r) hf ▸ Iff.rfl

/-- Nondegenerate simplices in the same dimension with meeting interiors are equal. -/
theorem orderNerveRealization_nonDegenerate_interior_eq {P : Type} [PartialOrder P]
    {n : ℕ} (s t : (nerve P).nonDegenerate n)
    (z w : SimplexCategory.toTop.obj (SimplexCategory.mk n))
    (hz : ∀ i, 0 < z.down.weights i) (hw : ∀ i, 0 < w.down.weights i)
    (h : orderNerveRealizationSimplex P s.val z = orderNerveRealizationSimplex P t.val w) :
    s = t := by
  have hrange := orderNerveRealizationSimplex_interior_range_eq s.val t.val z w hz hw h
  have hs := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s.val).mp s.property
  have ht := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono t.val).mp t.property
  have he := (hs.range_inj ht).mp hrange
  apply Subtype.ext
  exact CategoryTheory.Functor.ext (fun i => congrFun he i)

/-- Nondegenerate simplex interiors in different dimensions cannot meet. -/
theorem orderNerveRealization_nonDegenerate_interior_dimension_eq {P : Type}
    [PartialOrder P] {n m : ℕ} (s : (nerve P).nonDegenerate n)
    (t : (nerve P).nonDegenerate m)
    (z : SimplexCategory.toTop.obj (SimplexCategory.mk n))
    (w : SimplexCategory.toTop.obj (SimplexCategory.mk m))
    (hz : ∀ i, 0 < z.down.weights i) (hw : ∀ i, 0 < w.down.weights i)
    (h : orderNerveRealizationSimplex P s.val z = orderNerveRealizationSimplex P t.val w) :
    n = m := by
  have hrange := orderNerveRealizationSimplex_interior_range_eq s.val t.val z w hz hw h
  have hs := (PartialOrder.mem_nerve_nonDegenerate_iff_injective s.val).mp s.property
  have ht := (PartialOrder.mem_nerve_nonDegenerate_iff_injective t.val).mp t.property
  have hc := Nat.card_congr ((Equiv.ofInjective s.val.obj hs).trans
    ((Set.equivOfEq hrange).trans (Equiv.ofInjective t.val.obj ht).symm))
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin, SimplexCategory.len_mk] at hc
  omega

end FiniteChains.Comb
