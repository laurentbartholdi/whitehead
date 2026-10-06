module

public import RequestProject.OrderNerveOneDecoding
public import RequestProject.OrderThreeNormalization

@[expose] public section

/-! Strict cellular fillings give genuine fillings in the homogeneous full nerve. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

noncomputable def ordStrictInclusion1 : (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ]
    (OrdEdge P →₀ ℤ) := Finsupp.lmapDomain ℤ ℤ (strictOrderIncl P).onE

theorem ordNormalization_one_boundary (c : OrdEdge P →₀ ℤ) :
    bdry2 (orderCx P) (ordNormalizationHomotopy1 c) =
      c - ordStrictInclusion1 (normalizeOrdChain1 c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, map_add]; abel
  | single e n =>
    rcases e with ⟨⟨a, b⟩, hab⟩
    by_cases he : a = b
    · subst b
      simp [ordNormalizationHomotopy1, normalizeOrdChain1, normalizeOrdEdge,
        ordStrictInclusion1, bdry2, orderCx, pathChain]
    · simp [ordNormalizationHomotopy1, normalizeOrdChain1, normalizeOrdEdge,
        ordStrictInclusion1, strictOrderIncl, he]

theorem weak_oneCycle_filling_of_strict
    (hfill : ∀ c : StrictOrdEdge P →₀ ℤ, bdry1 (strictOrderCx P) c = 0 →
      ∃ y : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) y = c)
    (c : OrdEdge P →₀ ℤ) (hc : bdry1 (orderCx P) c = 0) :
    ∃ y : OrdTri P →₀ ℤ, bdry2 (orderCx P) y = c := by
  have hn : bdry1 (strictOrderCx P) (normalizeOrdChain1 c) = 0 := by
    rw [bdry1_normalizeOrdChain1, hc]
  obtain ⟨y, hy⟩ := hfill _ hn
  have hy' : bdry2 (orderCx P) (ordStrictInclusion2 y) =
      ordStrictInclusion1 (normalizeOrdChain1 c) := by
    change bdry2 (orderCx P) (chain2 (strictOrderIncl P) y) = _
    rw [bdry2_chain2, hy]
    rfl
  refine ⟨ordStrictInclusion2 y + ordNormalizationHomotopy1 c, ?_⟩
  rw [map_add, hy', ordNormalization_one_boundary]
  change ordStrictInclusion1 (normalizeOrdChain1 c) +
    (c - ordStrictInclusion1 (normalizeOrdChain1 c)) = c
  abel

def strictOrdTetWeak (t : StrictOrdTet P) : OrdTet P :=
  ⟨t.1, t.2.1.le, t.2.2.1.le, t.2.2.2.le⟩

theorem ordBoundary3_strict_inclusion (y : StrictOrdTet P →₀ ℤ) :
    ordBoundary3 (Finsupp.mapDomain strictOrdTetWeak y) =
      ordStrictInclusion2 (strictOrdBoundary3 y) := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [Finsupp.mapDomain_add, map_add, hc, hd, map_add, map_add]
  | single t n =>
    rw [Finsupp.mapDomain_single, ordBoundary3, Finsupp.linearCombination_single,
      strictOrdBoundary3, Finsupp.linearCombination_single, map_smul]
    congr 1
    simp only [strictOrdTetBoundary, map_sub, map_add]
    simp [ordTetBoundary, strictOrdTetWeak, ordStrictInclusion2, strictOrderIncl]

theorem weak_twoCycle_filling_of_strict
    (hfill : ∀ c : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) c = 0 →
      ∃ y : StrictOrdTet P →₀ ℤ, strictOrdBoundary3 y = c)
    (c : OrdTri P →₀ ℤ) (hc : bdry2 (orderCx P) c = 0) :
    ∃ y : OrdTet P →₀ ℤ, ordBoundary3 y = c := by
  obtain ⟨y, hy⟩ := hfill _ (normalizeOrdChain2_cycle c hc)
  refine ⟨Finsupp.mapDomain strictOrdTetWeak y + ordNormalizationHomotopy2 c, ?_⟩
  rw [map_add, ordBoundary3_strict_inclusion, hy, ← ordNormalization_cycle_boundary c hc]
  abel

theorem ordNerveChain3_mem_inc (c : OrdTet P →₀ ℤ) :
    ordNerveChain3 c ∈ Nerve.Inc P := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add] using AddSubgroup.add_mem _ hc hd
  | single t n =>
    simp only [ordNerveChain3, Finsupp.linearCombination_single]
    apply AddSubgroup.zsmul_mem
    apply Nerve.of_mem_inc
    simpa [List.isChain_cons] using t.2

theorem nerve_oneCycle_filling_of_strict
    (hfill : ∀ c : StrictOrdEdge P →₀ ℤ, bdry1 (strictOrderCx P) c = 0 →
      ∃ y : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) y = c)
    (c : Nerve.Ch P) (hi : c ∈ Nerve.Inc P)
    (hd : Nerve.lengthProjection 2 c = c) (hc : Nerve.bdry c = 0) :
    ∃ y ∈ Nerve.Inc P, Nerve.bdry y = c := by
  have he : ordNerveChain1 (decodeOrdNerve1 c) = c := by
    rw [ordNerveChain1_decode hi, hd]
  have hcyc : bdry1 (orderCx P) (decodeOrdNerve1 c) = 0 :=
    (ordNerveChain1_cycle_iff _).mp (by rw [he]; exact hc)
  obtain ⟨y, hy⟩ := weak_oneCycle_filling_of_strict hfill _ hcyc
  refine ⟨ordNerveChain2 y, ordNerveChain2_mem_inc y, ?_⟩
  rw [← ordNerveChain1_bdry2, hy, he]

theorem nerve_twoCycle_filling_of_strict
    (hfill : ∀ c : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) c = 0 →
      ∃ y : StrictOrdTet P →₀ ℤ, strictOrdBoundary3 y = c)
    (c : Nerve.Ch P) (hi : c ∈ Nerve.Inc P)
    (hd : Nerve.lengthProjection 3 c = c) (hc : Nerve.bdry c = 0) :
    ∃ y ∈ Nerve.Inc P, Nerve.bdry y = c := by
  have he : ordNerveChain2 (decodeOrdNerve2 c) = c := by
    rw [ordNerveChain2_decode hi, hd]
  have hcyc : bdry2 (orderCx P) (decodeOrdNerve2 c) = 0 :=
    (ordNerveChain2_cycle_iff _).mp (by rw [he]; exact hc)
  obtain ⟨y, hy⟩ := weak_twoCycle_filling_of_strict hfill _ hcyc
  refine ⟨ordNerveChain3 y, ordNerveChain3_mem_inc y, ?_⟩
  rw [← ordNerveChain2_ordBoundary3, hy, he]

end FiniteChains.Comb
