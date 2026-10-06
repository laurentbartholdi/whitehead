import RequestProject.QCubeThreeFacetCoordinates

/-! Integral coefficient calculation for the six oriented faces of an ordered three-cube.
The separate geometric comparison must identify this matrix with actual cube edge cells. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis

def fixedCoordinateSign (s : ZMod 2) : ℤ := if s = 0 then 1 else -1

noncomputable def threeFacetBoundaryColumn (i : Fin 3 × ZMod 2) :
    (Fin 3 × ZMod 2 × ZMod 2) →₀ ℤ :=
  if i.1 = 0 then
    -Finsupp.single (0, i.2, 0) 1 + Finsupp.single (0, i.2, 1) 1 +
      Finsupp.single (1, i.2, 0) 1 - Finsupp.single (1, i.2, 1) 1
  else if i.1 = 1 then
    -Finsupp.single (0, 0, i.2) 1 + Finsupp.single (0, 1, i.2) 1 +
      Finsupp.single (2, i.2, 0) 1 - Finsupp.single (2, i.2, 1) 1
  else
    -Finsupp.single (1, 0, i.2) 1 + Finsupp.single (1, 1, i.2) 1 +
      Finsupp.single (2, 0, i.2) 1 - Finsupp.single (2, 1, i.2) 1

noncomputable def threeFacetBoundaryMatrix : ((Fin 3 × ZMod 2) →₀ ℤ) →ₗ[ℤ]
    ((Fin 3 × ZMod 2 × ZMod 2) →₀ ℤ) :=
  Finsupp.linearCombination ℤ threeFacetBoundaryColumn

set_option maxHeartbeats 1000000

theorem threeFacetBoundaryMatrix_row0 (r : (Fin 3 × ZMod 2) →₀ ℤ) (s t : ZMod 2) :
    threeFacetBoundaryMatrix r (0, s, t) =
      -fixedCoordinateSign t * r (0, s) - fixedCoordinateSign s * r (1, t) := by
  classical
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r q hr hq => simp only [map_add, Finsupp.add_apply, hr, hq]; ring
  | single i n =>
      obtain ⟨e, u⟩ := i
      fin_cases e <;> fin_cases u <;> fin_cases s <;> fin_cases t <;>
        norm_num [threeFacetBoundaryMatrix, threeFacetBoundaryColumn, fixedCoordinateSign,
          Finsupp.single_apply, Prod.mk.injEq]

theorem threeFacetBoundaryMatrix_row1 (r : (Fin 3 × ZMod 2) →₀ ℤ) (s t : ZMod 2) :
    threeFacetBoundaryMatrix r (1, s, t) =
      fixedCoordinateSign t * r (0, s) - fixedCoordinateSign s * r (2, t) := by
  classical
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r q hr hq => simp only [map_add, Finsupp.add_apply, hr, hq]; ring
  | single i n =>
      obtain ⟨e, u⟩ := i
      fin_cases e <;> fin_cases u <;> fin_cases s <;> fin_cases t <;>
        norm_num [threeFacetBoundaryMatrix, threeFacetBoundaryColumn, fixedCoordinateSign,
          Finsupp.single_apply, Prod.mk.injEq]

theorem threeFacetBoundaryMatrix_row2 (r : (Fin 3 × ZMod 2) →₀ ℤ) (s t : ZMod 2) :
    threeFacetBoundaryMatrix r (2, s, t) =
      fixedCoordinateSign t * r (1, s) + fixedCoordinateSign s * r (2, t) := by
  classical
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r q hr hq => simp only [map_add, Finsupp.add_apply, hr, hq]; ring
  | single i n =>
      obtain ⟨e, u⟩ := i
      fin_cases e <;> fin_cases u <;> fin_cases s <;> fin_cases t <;>
        norm_num [threeFacetBoundaryMatrix, threeFacetBoundaryColumn, fixedCoordinateSign,
          Finsupp.single_apply, Prod.mk.injEq]

def threeFacetOrientation (i : Fin 3 × ZMod 2) : ℤ :=
  (if i.1 = 1 then -1 else 1) * fixedCoordinateSign i.2

theorem threeFacetBoundaryMatrix_kernel (r : (Fin 3 × ZMod 2) →₀ ℤ)
    (hr : threeFacetBoundaryMatrix r = 0) :
    ∀ i, r i = r (0, 0) * threeFacetOrientation i := by
  have h00 := congrArg (fun z : (Fin 3 × ZMod 2 × ZMod 2) →₀ ℤ => z (0, 0, 0)) hr
  have h10 := congrArg (fun z : (Fin 3 × ZMod 2 × ZMod 2) →₀ ℤ => z (1, 0, 0)) hr
  have h01 := congrArg (fun z : (Fin 3 × ZMod 2 × ZMod 2) →₀ ℤ => z (0, 1, 0)) hr
  have h02 := congrArg (fun z : (Fin 3 × ZMod 2 × ZMod 2) →₀ ℤ => z (0, 0, 1)) hr
  have h12 := congrArg (fun z : (Fin 3 × ZMod 2 × ZMod 2) →₀ ℤ => z (1, 0, 1)) hr
  simp only [threeFacetBoundaryMatrix_row0, threeFacetBoundaryMatrix_row1,
    Finsupp.zero_apply] at h00 h10 h01 h02 h12
  norm_num [fixedCoordinateSign] at h00 h10 h01 h02 h12
  rintro ⟨e, s⟩
  fin_cases e
  · fin_cases s
    · change r (0, 0) = r (0, 0) * (1 : ℤ)
      norm_num
    · change r (0, 1) = r (0, 0) * (-1 : ℤ)
      norm_num
      omega
  · fin_cases s
    · change r (1, 0) = r (0, 0) * (-1 : ℤ)
      norm_num
      omega
    · change r (1, 1) = r (0, 0) * (1 : ℤ)
      norm_num
      omega
  · fin_cases s
    · change r (2, 0) = r (0, 0) * (1 : ℤ)
      norm_num
      omega
    · change r (2, 1) = r (0, 0) * (-1 : ℤ)
      norm_num
      omega

theorem threeFacetBoundaryMatrix_zero_iff (r : (Fin 3 × ZMod 2) →₀ ℤ) :
    threeFacetBoundaryMatrix r = 0 ↔ ∃ k : ℤ, ∀ i, r i = k * threeFacetOrientation i := by
  constructor
  · intro h
    exact ⟨r (0, 0), threeFacetBoundaryMatrix_kernel r h⟩
  · rintro ⟨k, h⟩
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    ext i
    obtain ⟨e, s, t⟩ := i
    fin_cases e
    · change threeFacetBoundaryMatrix r (0, s, t) = 0
      rw [threeFacetBoundaryMatrix_row0, h (0, s), h (1, t)]
      norm_num [threeFacetOrientation]
      ring
    · change threeFacetBoundaryMatrix r (1, s, t) = 0
      rw [threeFacetBoundaryMatrix_row1, h (0, s), h (2, t)]
      norm_num [threeFacetOrientation, h21]
      ring
    · change threeFacetBoundaryMatrix r (2, s, t) = 0
      rw [threeFacetBoundaryMatrix_row2, h (1, s), h (2, t)]
      norm_num [threeFacetOrientation, h21]
      ring

end FiniteChains.Davis
