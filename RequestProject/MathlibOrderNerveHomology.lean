import RequestProject.MathlibOrderNerveCycles
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

namespace FiniteChains.Comb
open CategoryTheory
variable (P : Type) [PartialOrder P]

/-- The actual degree-three to degree-one segment of Mathlib's alternating-face complex. -/
noncomputable def mathlibOrderNerveShortComplex : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 2)
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 1)
    (by
      apply ModuleCat.hom_ext
      ext c
      exact mathlibOrderNerve_d2_d3 P c)

/-- The genuine order-cell quotient is linearly equivalent to Mathlib's
categorical homology of its actual alternating-face differential segment. -/
noncomputable def mathlibOrderNerveCategoricalH2Equiv :
    OrderNerveH2 P ≃ₗ[ℤ] (mathlibOrderNerveShortComplex P).homology :=
  (mathlibOrderNerveH2Equiv P).trans
    ((mathlibOrderNerveShortComplex P).moduleCatHomologyIso.symm.toLinearEquiv)

/-- The explicit differential segment is the actual degree-two short complex. -/
noncomputable def mathlibOrderNerveShortComplexIso :
    mathlibOrderNerveShortComplex P ≅
      (AlgebraicTopology.AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).sc 2 :=
  (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      change 𝟙 _ ≫ (AlgebraicTopology.AlternatingFaceMapComplex.obj
        (mathlibOrderNerveModule P)).d 3 2 =
          AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 2 ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
      exact AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ 2)
    (by
      change 𝟙 _ ≫ (AlgebraicTopology.AlternatingFaceMapComplex.obj
        (mathlibOrderNerveModule P)).d 2 1 =
          AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 1 ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
      exact AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ 1) :
      mathlibOrderNerveShortComplex P ≅
        (AlgebraicTopology.AlternatingFaceMapComplex.obj
          (mathlibOrderNerveModule P)).sc' 3 2 1) ≪≫
    ((AlgebraicTopology.AlternatingFaceMapComplex.obj
      (mathlibOrderNerveModule P)).isoSc' 3 2 1
        ((ComplexShape.down ℕ).prev_eq' (by decide : (ComplexShape.down ℕ).Rel 3 2))
        ((ComplexShape.down ℕ).next_eq' (by decide : (ComplexShape.down ℕ).Rel 2 1))).symm

/-- The order-cell quotient is the actual degree-two categorical homology of
Mathlib's alternating-face chain complex. -/
noncomputable def mathlibOrderNerveComplexH2Equiv :
    OrderNerveH2 P ≃ₗ[ℤ]
      (AlgebraicTopology.AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).homology 2 :=
  (mathlibOrderNerveCategoricalH2Equiv P).trans
    (((ShortComplex.homologyFunctor (ModuleCat ℤ)).mapIso
      (mathlibOrderNerveShortComplexIso P)).toLinearEquiv)

end FiniteChains.Comb
