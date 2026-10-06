import RequestProject.QCubeSquareInternalBoundary
import RequestProject.QCubeSquareCoefficientSigns

/-! The genuine square radial boundary matrix has one-dimensional integral kernel. -/
set_option maxHeartbeats 1000000

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb

theorem squareInternalBoundary_facet (z : (Bool × ZMod 2 × Bool) →₀ ℤ)
    (e : Bool) (s : ZMod 2) :
    squareInternalBoundary z (.inl (e, s)) = z (e, s, false) + z (e, s, true) := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, Finsupp.add_apply, hz, hw]; abel
  | single i n =>
      obtain ⟨f, t, b⟩ := i
      cases e <;> cases f <;> fin_cases s <;> fin_cases t <;> cases b <;>
        simp [squareInternalBoundary, Prod.mk.injEq]

theorem squareInternalBoundary_vertex (z : (Bool × ZMod 2 × Bool) →₀ ℤ)
    (s t : ZMod 2) :
    squareInternalBoundary z (.inr (s, t)) =
      -(z (true, s, decide (t = 0)) + z (false, t, decide (s = 0))) := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, Finsupp.add_apply, hz, hw]; abel
  | single i n =>
      obtain ⟨e, r, b⟩ := i
      cases e <;> fin_cases r <;> cases b <;> fin_cases s <;> fin_cases t <;>
        simp [squareInternalBoundary, squareFlagCornerIndex, Prod.mk.injEq]

theorem squareInternalBoundary_kernel (z : (Bool × ZMod 2 × Bool) →₀ ℤ)
    (hz : squareInternalBoundary z = 0) :
    ∀ i, z i = z (false, 0, false) * squareFlagSign i := by
  have hf00 := congrArg (fun w : SquareRadialIndex →₀ ℤ => w (.inl (false, 0))) hz
  have hf01 := congrArg (fun w : SquareRadialIndex →₀ ℤ => w (.inl (false, 1))) hz
  have hf10 := congrArg (fun w : SquareRadialIndex →₀ ℤ => w (.inl (true, 0))) hz
  have hf11 := congrArg (fun w : SquareRadialIndex →₀ ℤ => w (.inl (true, 1))) hz
  have hv00 := congrArg (fun w : SquareRadialIndex →₀ ℤ => w (.inr (0, 0))) hz
  have hv10 := congrArg (fun w : SquareRadialIndex →₀ ℤ => w (.inr (1, 0))) hz
  have hv01 := congrArg (fun w : SquareRadialIndex →₀ ℤ => w (.inr (0, 1))) hz
  simp only [squareInternalBoundary_facet, Finsupp.zero_apply] at hf00 hf01 hf10 hf11
  simp only [squareInternalBoundary_vertex, Finsupp.zero_apply] at hv00 hv10 hv01
  norm_num at hv00 hv10 hv01
  rintro ⟨e, s, f⟩
  cases e <;> fin_cases s <;> cases f <;> simp only [squareFlagSign] <;> norm_num <;> omega

/-- An actual square-supported chain with zero internal boundary is its coefficient times
that square's genuine strict subdivision. -/
theorem squareChain_eq_scalar_subdivision {V : Type} [DecidableEq V] {A : CommRel V}
    (c : QCube A) (a b : V) (hne : a ≠ b) (hs : c.spx = {a, b})
    (z : (strictOrderCx (QCube A)).F →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2.2 = c)
    (hint : squareRadialCoordinates c a b hne hs
      (Comb.bdry2 (strictOrderCx (QCube A)) z) = 0) :
    z = z (squareFlag c a b hne hs (false, 0, false)) • cubeSquareSubdivision c a b hne hs := by
  let r := squareFlagCoordinates c a b hne hs z
  have hr : squareInternalBoundary r = 0 := by
    rw [← squareInternalBoundary_naturality c a b hne hs r]
    rw [squareFlagCoordinates_reconstruct c a b hne hs z hz]
    exact hint
  have he : r = r (false, 0, false) •
      squareFlagCoordinates c a b hne hs (cubeSquareSubdivision c a b hne hs) := by
    ext i
    rw [Finsupp.smul_apply, squareFlagCoordinates_apply c a b hne hs
      (cubeSquareSubdivision c a b hne hs) i, squareSubdivision_flag_coefficient, smul_eq_mul]
    exact squareInternalBoundary_kernel r hr i
  let f := Finsupp.lmapDomain ℤ ℤ (squareFlag c a b hne hs)
  have hzr : f r = z := squareFlagCoordinates_reconstruct c a b hne hs z hz
  have hsr : f (squareFlagCoordinates c a b hne hs (cubeSquareSubdivision c a b hne hs)) =
      cubeSquareSubdivision c a b hne hs := by
    apply squareFlagCoordinates_reconstruct
    intro t ht
    by_contra htop
    exact (Finsupp.mem_support_iff.mp ht)
      (cubeSquareSubdivision_eq_zero_off_top c a b hne hs t htop)
  calc
    z = f r := hzr.symm
    _ = f (r (false, 0, false) •
        squareFlagCoordinates c a b hne hs (cubeSquareSubdivision c a b hne hs)) := congrArg f he
    _ = r (false, 0, false) • cubeSquareSubdivision c a b hne hs := by rw [map_smul, hsr]
    _ = _ := rfl

end FiniteChains.Davis
