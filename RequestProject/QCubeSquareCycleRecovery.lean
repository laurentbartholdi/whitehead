import RequestProject.QCubeSquareBoundaryKernel

/-! Local recovery of cubical coefficients from actual two-dimensional strict cycles. -/
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

theorem squareRadialBoundary_off_square (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (t : (strictOrderCx (QCube A)).F)
    (hm : t.1.2.1 ≠ c) (ht : t.1.2.2 ≠ c) (n : ℤ) :
    squareRadialCoordinates c a b hne hs
      (Comb.bdry2 (strictOrderCx (QCube A)) (Finsupp.single t n)) = 0 := by
  let e01 : (strictOrderCx (QCube A)).E := ⟨(t.1.1, t.1.2.1), t.2.1⟩
  let e12 : (strictOrderCx (QCube A)).E := ⟨(t.1.2.1, t.1.2.2), t.2.2⟩
  let e02 : (strictOrderCx (QCube A)).E := ⟨(t.1.1, t.1.2.2), t.2.1.trans t.2.2⟩
  have hb : Comb.bdry2 (strictOrderCx (QCube A)) (Finsupp.single t 1) =
      Finsupp.single e01 1 + Finsupp.single e12 1 - Finsupp.single e02 1 := by
    simp [Comb.bdry2, strictOrderCx, pathChain, e01, e12, e02]
    abel
  have hn : Finsupp.single t n = n • Finsupp.single t 1 := by simp
  rw [hn, map_smul, map_smul, hb, map_sub, map_add,
    squareRadialCoordinates_off_top c a b hne hs e01 hm,
    squareRadialCoordinates_off_top c a b hne hs e12 ht,
    squareRadialCoordinates_off_top c a b hne hs e02 ht]
  simp

theorem squareRadialBoundary_filter_top (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (z : (strictOrderCx (QCube A)).F →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2.2.spx.card ≤ 2) :
    squareRadialCoordinates c a b hne hs (Comb.bdry2 (strictOrderCx (QCube A)) z) =
    squareRadialCoordinates c a b hne hs (Comb.bdry2 (strictOrderCx (QCube A))
      (z.filter (fun t => t.1.2.2 = c))) := by
  classical
  have hc : c.spx.card = 2 := by rw [hs]; simp [hne]
  conv_lhs => rw [← z.sum_single]
  conv_rhs => rw [← z.sum_single]
  simp only [Finsupp.sum, map_sum, Finsupp.filter_sum]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases he : t.1.2.2 = c
  · rw [Finsupp.filter_single_of_pos (fun t : (strictOrderCx (QCube A)).F => t.1.2.2 = c) he]
  · rw [Finsupp.filter_single_of_neg (fun t : (strictOrderCx (QCube A)).F => t.1.2.2 = c) he]
    have hm : t.1.2.1 ≠ c := by
      intro hm
      have hdim := (qCube_triangle_dimensions t (hz t ht)).2.1
      rw [hm, hc] at hdim
      omega
    rw [squareRadialBoundary_off_square c a b hne hs t hm he, map_zero, map_zero]

/-- Every genuine two-dimensional cycle has on each square exactly its cubical coefficient
 times the actual strict square subdivision. -/
theorem cubeTwoCycle_square_component (c : QCube A) (a b : V) (hne : a ≠ b)
    (hs : c.spx = {a, b}) (z : (strictOrderCx (QCube A)).F →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2.2.spx.card ≤ 2)
    (hcycle : Comb.bdry2 (strictOrderCx (QCube A)) z = 0) :
    z.filter (fun t => t.1.2.2 = c) =
      z (squareFlag c a b hne hs (false, 0, false)) • cubeSquareSubdivision c a b hne hs := by
  have hsupp : ∀ t ∈ (z.filter (fun t => t.1.2.2 = c)).support, t.1.2.2 = c := by
    intro t ht
    change t ∈ z.support.filter (fun t => t.1.2.2 = c) at ht
    exact (Finset.mem_filter.mp ht).2
  have hint : squareRadialCoordinates c a b hne hs
      (Comb.bdry2 (strictOrderCx (QCube A)) (z.filter (fun t => t.1.2.2 = c))) = 0 := by
    rw [← squareRadialBoundary_filter_top c a b hne hs z hz, hcycle, map_zero]
  have he := squareChain_eq_scalar_subdivision c a b hne hs _ hsupp hint
  simpa only [Finsupp.filter_apply, squareFlag_top, if_true] using he

end FiniteChains.Davis
