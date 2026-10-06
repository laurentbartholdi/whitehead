import RequestProject.OrderAcyclicRegularCover
import RequestProject.OrderTwoDimensionalH2Injection

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology
variable {P : Type} [PartialOrder P]

/-- Zero actual singular H1 produces finite weak order-chain fillings. -/
theorem weak_oneCycle_filling_of_singular_homology_zero
    (hH : Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)))
    (c : OrdEdge P →₀ ℤ) (hc : bdry1 (orderCx P) c = 0) :
    ∃ b : OrdTri P →₀ ℤ, bdry2 (orderCx P) b = c := by
  let K := AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)
  have he : K.ExactAt 1 := by
    apply (HomologicalComplex.exactAt_iff_isZero_homology K 1).mpr
    exact hH.of_iso (orderNervePositiveSingularHomologyIso P 0)
  rw [HomologicalComplex.exactAt_iff' (K := K) (i := 2) (j := 1) (k := 0)
    (ChainComplex.prev ℕ 1) (ChainComplex.next_nat_succ 0)] at he
  have hex := (ShortComplex.moduleCat_exact_iff _).mp he
  let z := ordNerveChain1 c
  have hz : z ∈ Nerve.Inc P := ordNerveChain1_mem_inc c
  have hlen : Nerve.lengthProjection 2 z = z := ordNerveChain1_lengthProjection c
  have hz0 : Nerve.bdry z = 0 := (ordNerveChain1_cycle_iff c).mpr hc
  have hd : K.d 1 0 (orderNerveGradedDecode 1 z) = 0 := by
    rw (config := { transparency := .default }) [AlternatingFaceMapComplex.obj_d_eq]
    change (AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 0).hom
      (orderNerveGradedDecode 1 z) = 0
    apply orderNerveGradedEncode_injective 0
    rw (config := { transparency := .default }) [map_zero, orderNerveGradedEncode_boundary,
      orderNerveGradedEncode_decode 1 hz, hlen, hz0]
  obtain ⟨a, ha⟩ := hex (orderNerveGradedDecode 1 z) hd
  change K.d 2 1 a = orderNerveGradedDecode 1 z at ha
  rw (config := { transparency := .default }) [AlternatingFaceMapComplex.obj_d_eq] at ha
  change (AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 1).hom a =
    orderNerveGradedDecode 1 z at ha
  have haInc : orderNerveGradedEncode 2 a ∈ Nerve.Inc P := by
    clear ha
    induction a using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simpa only [map_add] using AddSubgroup.add_mem _ hx hy
    | single s r =>
      rw (config := { transparency := .default }) [orderNerveGradedEncode_single]
      exact AddSubgroup.zsmul_mem _ (Nerve.of_mem_inc (orderNerveVertexList_chain s)) r
  refine ⟨decodeOrdNerve2 (orderNerveGradedEncode 2 a), ?_⟩
  apply ordNerveChain1_injective
  rw (config := { transparency := .default }) [ordNerveChain1_bdry2,
    ordNerveChain2_decode haInc,
    orderNerveGradedEncode_length, ← orderNerveGradedEncode_boundary, ha,
    orderNerveGradedEncode_decode 1 hz, hlen]

/-- The genuine H1-zero condition is equivalent to strict cellular one-cycle
fillability; all maps between weak, normalized and singular chains are proved. -/
theorem orderRealization_homology_one_isZero_iff_strict_fillings :
    Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)) ↔
      ∀ c : StrictOrdEdge P →₀ ℤ, bdry1 (strictOrderCx P) c = 0 →
        ∃ b : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) b = c := by
  constructor
  · intro hH c hc
    have hd : bdry1 (orderCx P) (chain1 (strictOrderIncl P) c) = 0 := by
      rw (config := { transparency := .default }) [bdry1_chain1, hc, map_zero]
    obtain ⟨b, hb⟩ := weak_oneCycle_filling_of_singular_homology_zero hH _ hd
    refine ⟨normalizeOrdChain2 b, ?_⟩
    rw (config := { transparency := .default }) [bdry2_normalizeOrdChain2, hb]
    exact normalizeOrdChain1_inclusion c
  · exact orderRealization_homology_one_isZero_of_strict_fillings

/-- In dimension two a strict two-cycle can be zero in actual singular
homology only if every coefficient is zero. -/
theorem strict_twoCycle_eq_zero_of_singular_homology_zero [(nerve P).HasDimensionLE 2]
    (hH : Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)))
    (c : StrictOrdTri P →₀ ℤ) (hc : bdry2 (strictOrderCx P) c = 0) : c = 0 := by
  letI := ModuleCat.subsingleton_of_isZero hH
  have hi : bdry2 (orderCx P) (chain2 (strictOrderIncl P) c) = 0 := by
    rw (config := { transparency := .default }) [bdry2_chain2, hc, map_zero]
  have hz : orderNerveH2Class P (chain2 (strictOrderIncl P) c) hi = 0 := by
    apply (orderCellSingularH2Equiv P).injective
    exact Subsingleton.elim _ _
  obtain ⟨b, hb⟩ := (orderNerveH2Class_eq_zero_iff P _ hi).mp hz
  have hn := congrArg normalizeOrdChain2 hb
  rw (config := { transparency := .default }) [normalizeOrdBoundary3_eq_zero_of_dimension_two] at hn
  have he : normalizeOrdChain2 (chain2 (strictOrderIncl P) c) = c :=
    normalizeOrdChain2_inclusion c
  exact (hn.trans he).symm

theorem orderRealization_homology_two_isZero_iff_strict_cycles_zero
    [(nerve P).HasDimensionLE 2] :
    Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)) ↔
      ∀ c : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) c = 0 → c = 0 :=
  ⟨strict_twoCycle_eq_zero_of_singular_homology_zero,
    orderRealization_homology_two_isZero_of_strict_cycles_zero P⟩

end FiniteChains.Comb
