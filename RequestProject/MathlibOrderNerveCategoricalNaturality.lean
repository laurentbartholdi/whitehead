module

public import RequestProject.MathlibOrderNerveHomology
public import RequestProject.MathlibOrderNerveCycleNaturality

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory CategoryTheory.Limits
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

/-- The actual monotone-map chain morphism on the degree-two differential segment. -/
noncomputable def mathlibOrderNerveShortComplexMap (f : P → Q) (hf : Monotone f) :
    mathlibOrderNerveShortComplex P ⟶ mathlibOrderNerveShortComplex Q where
  τ₁ := (mathlibOrderNerveChainMap f hf).f 3
  τ₂ := (mathlibOrderNerveChainMap f hf).f 2
  τ₃ := (mathlibOrderNerveChainMap f hf).f 1
  comm₁₂ := by
    have h := (mathlibOrderNerveChainMap f hf).comm 3 2
    simpa only [mathlibOrderNerveShortComplex, AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq, AlgebraicTopology.AlternatingFaceMapComplex.objD] using h
  comm₂₃ := by
    have h := (mathlibOrderNerveChainMap f hf).comm 2 1
    simpa only [mathlibOrderNerveShortComplex, AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq, AlgebraicTopology.AlternatingFaceMapComplex.objD] using h

/-- Actual cycle and quotient maps form Mathlib's verified homology map data. -/
noncomputable def mathlibOrderNerveLeftHomologyMapData (f : P → Q) (hf : Monotone f) :
    ShortComplex.LeftHomologyMapData (mathlibOrderNerveShortComplexMap f hf)
      (mathlibOrderNerveShortComplex P).moduleCatLeftHomologyData
      (mathlibOrderNerveShortComplex Q).moduleCatLeftHomologyData where
  φK := ModuleCat.ofHom (mathlibOrderNerveCycleMap f hf)
  φH := ModuleCat.ofHom (mathlibOrderNerveQuotientH2Map f hf)
  commi := by
    apply ModuleCat.hom_ext
    ext c
    rfl
  commf' := by
    apply ModuleCat.hom_ext
    ext c
    apply Subtype.ext
    have h := congrArg (fun m :
      ModuleCat.of ℤ (ComposableArrows P 3 →₀ ℤ) ⟶
        ModuleCat.of ℤ (ComposableArrows Q 2 →₀ ℤ) => m c)
      (mathlibOrderNerveShortComplexMap f hf).comm₁₂
    exact h.symm
  commπ := by
    apply ModuleCat.hom_ext
    ext c
    rfl

/-- The actual categorical homology map is conjugate to the genuine differential quotient map. -/
theorem mathlibOrderNerve_homologyMap_eq (f : P → Q) (hf : Monotone f) :
    ShortComplex.homologyMap (mathlibOrderNerveShortComplexMap f hf) =
      (mathlibOrderNerveShortComplex P).moduleCatHomologyIso.hom ≫
        ModuleCat.ofHom (mathlibOrderNerveQuotientH2Map f hf) ≫
          (mathlibOrderNerveShortComplex Q).moduleCatHomologyIso.inv :=
  (mathlibOrderNerveLeftHomologyMapData f hf).homologyMap_eq

/-- A proved zero order-homology map gives the zero actual categorical homology map. -/
theorem mathlibOrderNerve_homologyMap_zero (f : P → Q) (hf : Monotone f)
    (hzero : orderNerveH2Map f hf = 0) :
    ShortComplex.homologyMap (mathlibOrderNerveShortComplexMap f hf) = 0 := by
  rw [mathlibOrderNerve_homologyMap_eq,
    mathlibOrderNerveQuotientH2Map_zero f hf hzero]
  change _ ≫ (0 : (mathlibOrderNerveShortComplex P).moduleCatLeftHomologyData.H ⟶
    (mathlibOrderNerveShortComplex Q).moduleCatLeftHomologyData.H) ≫ _ = 0
  rw [zero_comp, comp_zero]

/-- The categorical homology comparison commutes with the actual monotone-map homology map. -/
theorem mathlibOrderNerveCategoricalH2Equiv_natural (f : P → Q) (hf : Monotone f)
    (z : OrderNerveH2 P) :
    (ShortComplex.homologyMap (mathlibOrderNerveShortComplexMap f hf)).hom
      (mathlibOrderNerveCategoricalH2Equiv P z) =
        mathlibOrderNerveCategoricalH2Equiv Q (orderNerveH2Map f hf z) := by
  rw [mathlibOrderNerve_homologyMap_eq]
  change (mathlibOrderNerveShortComplex Q).moduleCatHomologyIso.symm.toLinearEquiv
    (mathlibOrderNerveQuotientH2Map f hf
      ((mathlibOrderNerveShortComplex P).moduleCatHomologyIso.toLinearEquiv
        ((mathlibOrderNerveShortComplex P).moduleCatHomologyIso.toLinearEquiv.symm
          (mathlibOrderNerveH2Equiv P z)))) = _
  rw [LinearEquiv.apply_symm_apply, mathlibOrderNerveH2Equiv_natural]
  rfl

end FiniteChains.Comb
