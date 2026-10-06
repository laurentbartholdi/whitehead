module

public import RequestProject.MathlibOrderNerveNaturality
public import RequestProject.MathlibOrderNerveCycles
public import RequestProject.OrderNerveH2Maps

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

/-- The genuine Mathlib chain map preserves its actual two-cycle kernel. -/
theorem mathlibOrderNerveChainMap_cycle (f : P → Q) (hf : Monotone f)
    (c : LinearMap.ker ((AlgebraicTopology.AlternatingFaceMapComplex.objD
      (mathlibOrderNerveModule P) 1).hom)) :
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule Q) 1).hom
      (((mathlibOrderNerveChainMap f hf).f 2).hom c.val) = 0 := by
  let d := (mathlibOrderNerveCycleEquiv P).symm c
  have he := congrArg Subtype.val ((mathlibOrderNerveCycleEquiv P).apply_symm_apply c)
  change (Finsupp.domLCongr (R := ℤ) (M := ℤ) (ordTriNerveEquiv P)) d.val = c.val at he
  simp only [Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_eq_mapDomain] at he
  have h := mathlibOrderNerveChainMap_two f hf d.val
  rw [he] at h
  rw [h, mathlibOrderNerve_d2, bdry2_chain2, d.property, map_zero,
    Finsupp.mapDomain_zero]

/-- The actual Mathlib chain map restricted to genuine two-cycles. -/
noncomputable def mathlibOrderNerveCycleMap (f : P → Q) (hf : Monotone f) :
    LinearMap.ker ((AlgebraicTopology.AlternatingFaceMapComplex.objD
      (mathlibOrderNerveModule P) 1).hom) →ₗ[ℤ]
    LinearMap.ker ((AlgebraicTopology.AlternatingFaceMapComplex.objD
      (mathlibOrderNerveModule Q) 1).hom) where
  toFun c := ⟨((mathlibOrderNerveChainMap f hf).f 2).hom c.val,
    mathlibOrderNerveChainMap_cycle f hf c⟩
  map_add' c d := Subtype.ext (map_add ((mathlibOrderNerveChainMap f hf).f 2).hom c.val d.val)
  map_smul' n c := Subtype.ext (map_smul ((mathlibOrderNerveChainMap f hf).f 2).hom n c.val)

/-- The actual cycle-kernel comparison is natural under monotone maps. -/
theorem mathlibOrderNerveCycleEquiv_natural (f : P → Q) (hf : Monotone f)
    (c : LinearMap.ker (FiniteChains.Comb.bdry2 (orderCx P))) :
    mathlibOrderNerveCycleMap f hf (mathlibOrderNerveCycleEquiv P c) =
      mathlibOrderNerveCycleEquiv Q (orderNerveCycleMap f hf c) := by
  apply Subtype.ext
  change ((mathlibOrderNerveChainMap f hf).f 2).hom
      ((Finsupp.domLCongr (R := ℤ) (M := ℤ) (ordTriNerveEquiv P)) c.val) =
    (Finsupp.domLCongr (R := ℤ) (M := ℤ) (ordTriNerveEquiv Q))
      (chain2 (orderCxMap f hf) c.val)
  simp only [Finsupp.domLCongr_apply, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_eq_mapDomain]
  exact mathlibOrderNerveChainMap_two f hf c.val

/-- The actual Mathlib cycle map preserves the actual three-boundary range. -/
theorem mathlibOrderNerveCycleMap_boundaries (f : P → Q) (hf : Monotone f) :
    LinearMap.range (mathlibOrderNerveBoundary3Cycles P) ≤
      (LinearMap.range (mathlibOrderNerveBoundary3Cycles Q)).comap
        (mathlibOrderNerveCycleMap f hf) := by
  rintro c ⟨y, rfl⟩
  obtain ⟨d, rfl⟩ := Finsupp.mapDomain_surjective (ordTetNerveEquiv P).surjective y
  refine ⟨((mathlibOrderNerveChainMap f hf).f 3).hom
    (Finsupp.mapDomain (ordTetNerveEquiv P) d), ?_⟩
  apply Subtype.ext
  change (AlgebraicTopology.AlternatingFaceMapComplex.objD
      (mathlibOrderNerveModule Q) 2).hom
      (((mathlibOrderNerveChainMap f hf).f 3).hom
        (Finsupp.mapDomain (ordTetNerveEquiv P) d)) =
    ((mathlibOrderNerveChainMap f hf).f 2).hom
      ((AlgebraicTopology.AlternatingFaceMapComplex.objD
        (mathlibOrderNerveModule P) 2).hom
          (Finsupp.mapDomain (ordTetNerveEquiv P) d))
  rw [mathlibOrderNerveChainMap_three, mathlibOrderNerve_d3,
    mathlibOrderNerve_d3, mathlibOrderNerveChainMap_two, chain2_ordBoundary3]

/-- The map on genuine Mathlib differential homology quotients induced by the actual chain map. -/
noncomputable def mathlibOrderNerveQuotientH2Map (f : P → Q) (hf : Monotone f) :
    (LinearMap.ker ((AlgebraicTopology.AlternatingFaceMapComplex.objD
      (mathlibOrderNerveModule P) 1).hom) ⧸
        LinearMap.range (mathlibOrderNerveBoundary3Cycles P)) →ₗ[ℤ]
    (LinearMap.ker ((AlgebraicTopology.AlternatingFaceMapComplex.objD
      (mathlibOrderNerveModule Q) 1).hom) ⧸
        LinearMap.range (mathlibOrderNerveBoundary3Cycles Q)) :=
  (LinearMap.range (mathlibOrderNerveBoundary3Cycles P)).mapQ
    (LinearMap.range (mathlibOrderNerveBoundary3Cycles Q))
    (mathlibOrderNerveCycleMap f hf) (mathlibOrderNerveCycleMap_boundaries f hf)

/-- The actual homology-quotient comparison is natural under monotone maps. -/
theorem mathlibOrderNerveH2Equiv_natural (f : P → Q) (hf : Monotone f)
    (z : OrderNerveH2 P) :
    mathlibOrderNerveQuotientH2Map f hf (mathlibOrderNerveH2Equiv P z) =
      mathlibOrderNerveH2Equiv Q (orderNerveH2Map f hf z) := by
  induction z using Submodule.Quotient.induction_on with
  | H c =>
    change Submodule.Quotient.mk
      (mathlibOrderNerveCycleMap f hf (mathlibOrderNerveCycleEquiv P c)) =
        Submodule.Quotient.mk
          (mathlibOrderNerveCycleEquiv Q (orderNerveCycleMap f hf c))
    rw [mathlibOrderNerveCycleEquiv_natural]

/-- A proved zero homology map transports to the genuine Mathlib differential quotient map. -/
theorem mathlibOrderNerveQuotientH2Map_zero (f : P → Q) (hf : Monotone f)
    (hzero : orderNerveH2Map f hf = 0) :
    mathlibOrderNerveQuotientH2Map f hf = 0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨w, rfl⟩ := (mathlibOrderNerveH2Equiv P).surjective z
  rw [mathlibOrderNerveH2Equiv_natural, hzero, LinearMap.zero_apply, (mathlibOrderNerveH2Equiv Q).map_zero,
    LinearMap.zero_apply]

end FiniteChains.Comb
