module

public import RequestProject.Fox

@[expose] public section

/-!
# The acyclic presentation of Remark 2

Remark 2 exhibits the presentation

  `A = ⟨x, y | x²yx⁻¹y, xy⁴xy⁻¹⟩`

whose exponent-sum matrix is `!![1, 2; 2, 3]`, of determinant `-1`; hence the
two-complex `K(A)` is acyclic.  (That `G(A) ≅ SL(2,5)`, and hence that `K(A)`
is not aspherical, is quoted from the literature and is not formalized here.)

For a presentation with equally many generators and relators the cellular chain
complex of the standard two-complex is `ℤ^J → ℤ^I → ℤ → 0`, the first map given
by the exponent-sum matrix `M` and the second map zero; so the complex is
acyclic exactly when `M` is invertible over `ℤ`.  This is what is proved below:
`H₂ = ker M = 0` and `H₁ = coker M = 0`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open Matrix

/-- The first generator `x`. -/
def genX : FreeGroup (Fin 2) := FreeGroup.of 0

/-- The second generator `y`. -/
def genY : FreeGroup (Fin 2) := FreeGroup.of 1

/-- The two relators of the presentation `A` of Remark 2. -/
def relA : Fin 2 → FreeGroup (Fin 2)
  | 0 => genX * genX * genY * genX⁻¹ * genY
  | 1 => genX * genY ^ 4 * genX * genY⁻¹

/-- The exponent-sum matrix of Remark 2: the `(i, j)` entry is the exponent sum of the
`i`-th generator in the `j`-th relator. -/
def expMatrixA : Matrix (Fin 2) (Fin 2) ℤ := !![1, 2; 2, 3]

/-- The entries of `expMatrixA` really are the exponent sums of the relators. -/
theorem expMatrixA_eq (i j : Fin 2) :
    expMatrixA i j = Multiplicative.toAdd (expSum i (relA j)) := by
  fin_cases i <;> fin_cases j <;>
    simp [expMatrixA, relA, genX, genY, expSum, FreeGroup.lift_apply_of, map_mul, map_inv, map_pow]

/-- Equivalently, by `aug_fox`, the entries are the augmented Fox derivatives of the
relators, i.e. the Fox boundary of Remark 1 taken over the trivial quotient. -/
theorem expMatrixA_eq_aug_fox (i j : Fin 2) :
    expMatrixA i j = aug (fox i (relA j)) := by
  rw [expMatrixA_eq, aug_fox]

/-- The determinant of the exponent-sum matrix is `-1`. -/
theorem det_expMatrixA : expMatrixA.det = -1 := by
  simp [expMatrixA, Matrix.det_fin_two_of]

/-- The exponent-sum map is bijective: `K(A)` is acyclic. -/
theorem bijective_expMatrixA : Function.Bijective (expMatrixA.mulVecLin) := by
  have hdet : IsUnit expMatrixA.det := by rw [det_expMatrixA]; exact isUnit_one.neg
  refine Function.bijective_iff_has_inverse.mpr ⟨(expMatrixA⁻¹).mulVec, ?_, ?_⟩
  · intro v
    change expMatrixA⁻¹ *ᵥ (expMatrixA *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  · intro v
    change expMatrixA *ᵥ (expMatrixA⁻¹ *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-- `H₂(K(A)) = ker M = 0`. -/
theorem injective_expMatrixA : Function.Injective (expMatrixA.mulVecLin) :=
  bijective_expMatrixA.1

/-- `H₁(K(A)) = coker M = 0`. -/
theorem surjective_expMatrixA : Function.Surjective (expMatrixA.mulVecLin) :=
  bijective_expMatrixA.2

end FiniteChains
