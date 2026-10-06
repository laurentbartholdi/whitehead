module

public import RequestProject.StrictOrderChains

@[expose] public section

/-! Explicit degree-two normalization homotopy in the full weak order nerve. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def OrdTet (P : Type u) [PartialOrder P] :=
  {t : P × P × P × P // t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2.1 ∧ t.2.2.1 ≤ t.2.2.2}

noncomputable def ordTetBoundary (t : OrdTet P) : OrdTri P →₀ ℤ :=
  Finsupp.single ⟨(t.1.2.1, t.1.2.2.1, t.1.2.2.2), t.2.2⟩ 1 -
  Finsupp.single ⟨(t.1.1, t.1.2.2.1, t.1.2.2.2), t.2.1.trans t.2.2.1, t.2.2.2⟩ 1 +
  Finsupp.single ⟨(t.1.1, t.1.2.1, t.1.2.2.2), t.2.1, t.2.2.1.trans t.2.2.2⟩ 1 -
  Finsupp.single ⟨(t.1.1, t.1.2.1, t.1.2.2.1), t.2.1, t.2.2.1⟩ 1

noncomputable def ordBoundary3 : (OrdTet P →₀ ℤ) →ₗ[ℤ] (OrdTri P →₀ ℤ) :=
  Finsupp.linearCombination ℤ ordTetBoundary

/-- The alternating three-simplex boundary is a genuine cellular two-cycle. -/
theorem bdry2_ordTetBoundary (t : OrdTet P) :
    bdry2 (orderCx P) (ordTetBoundary t) = 0 := by
  simp only [ordTetBoundary, map_sub, map_add, bdry2_single (X := orderCx P), one_smul]
  simp [orderCx, pathChain]
  all_goals abel

theorem bdry2_ordBoundary3 (c : OrdTet P →₀ ℤ) :
    bdry2 (orderCx P) (ordBoundary3 c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd, add_zero]
  | single t n =>
    simp only [ordBoundary3, Finsupp.linearCombination_single, map_smul,
      bdry2_ordTetBoundary, smul_zero]

noncomputable def ordNormalizationHomotopy1 : (OrdEdge P →₀ ℤ) →ₗ[ℤ]
    (OrdTri P →₀ ℤ) := by
  classical
  exact Finsupp.linearCombination ℤ (fun e =>
    if e.1.1 = e.1.2 then
      Finsupp.single ⟨(e.1.1, e.1.1, e.1.1), le_rfl, le_rfl⟩ 1 else 0)

noncomputable def ordNormalizationTriangleHomotopy (t : OrdTri P) : OrdTet P →₀ ℤ := by
  classical
  exact if h : t.1.1 = t.1.2.1 then
    Finsupp.single ⟨(t.1.1, t.1.1, t.1.1, t.1.2.2), le_rfl, le_rfl,
      h ▸ t.2.2⟩ 1 else if h' : t.1.2.1 = t.1.2.2 then
    -Finsupp.single ⟨(t.1.1, t.1.2.1, t.1.2.1, t.1.2.1), t.2.1, le_rfl, le_rfl⟩ 1
    else 0

noncomputable def ordNormalizationHomotopy2 : (OrdTri P →₀ ℤ) →ₗ[ℤ]
    (OrdTet P →₀ ℤ) :=
  Finsupp.linearCombination ℤ ordNormalizationTriangleHomotopy

/-- The discrepancy on a triangle is an explicit three-boundary plus the homotopy of
its edge boundary. This includes triangles with coinciding vertices. -/
theorem ordNormalization_triangle_identity (t : OrdTri P) :
    Finsupp.single t (1 : ℤ) -
      (Finsupp.mapDomain (strictOrderIncl P).onF (normalizeOrdTriangle t) : OrdTri P →₀ ℤ) =
    ordNormalizationHomotopy1 (pathChain ((orderCx P).att t)) +
      ordBoundary3 (ordNormalizationTriangleHomotopy t) := by
  classical
  rcases t with ⟨⟨a, b, c⟩, hab, hbc⟩
  by_cases heab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      simp [normalizeOrdTriangle, ordNormalizationHomotopy1, pathChain, orderCx,
        ordNormalizationTriangleHomotopy, ordBoundary3, ordTetBoundary]
    · simp [normalizeOrdTriangle, ordNormalizationHomotopy1, pathChain, orderCx,
        ordNormalizationTriangleHomotopy, ordBoundary3, ordTetBoundary]
  · by_cases hebc : b = c
    · subst c
      simp [normalizeOrdTriangle, ordNormalizationHomotopy1, pathChain, orderCx,
        ordNormalizationTriangleHomotopy, ordBoundary3, ordTetBoundary, heab]
    · have hab' : a < b := lt_of_le_of_ne hab heab
      have hbc' : b < c := lt_of_le_of_ne hbc hebc
      simp [normalizeOrdTriangle, strictOrderIncl, ordNormalizationHomotopy1,
        pathChain, orderCx, ordNormalizationTriangleHomotopy, ordBoundary3,
        hab', hbc', heab, hebc, (hab'.trans hbc').ne]

/-- The inclusion on strict two-chains, as an integer-linear map. -/
noncomputable def ordStrictInclusion2 : (StrictOrdTri P →₀ ℤ) →ₗ[ℤ]
    (OrdTri P →₀ ℤ) := Finsupp.lmapDomain ℤ ℤ (strictOrderIncl P).onF

/-- The explicit normalization homotopy on arbitrary finitely supported two-chains. -/
theorem ordNormalization_chain_identity (c : OrdTri P →₀ ℤ) :
    c - ordStrictInclusion2 (normalizeOrdChain2 c) =
    ordNormalizationHomotopy1 (bdry2 (orderCx P) c) +
      ordBoundary3 (ordNormalizationHomotopy2 c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [map_add]
    rw [add_sub_add_comm, hc, hd]
    abel
  | single t n =>
    rw [bdry2_single]
    have h := congrArg (fun x : OrdTri P →₀ ℤ => n • x)
      (ordNormalization_triangle_identity t)
    simpa [ordStrictInclusion2, ordNormalizationHomotopy2, smul_sub,
      smul_add, Finsupp.smul_single] using h

/-- A cellular two-cycle differs from its normalized image by an explicit three-boundary
in the full order nerve. No identification of the truncated second homotopy groups is used. -/
theorem ordNormalization_cycle_boundary (c : OrdTri P →₀ ℤ)
    (hc : bdry2 (orderCx P) c = 0) :
    c - ordStrictInclusion2 (normalizeOrdChain2 c) =
      ordBoundary3 (ordNormalizationHomotopy2 c) := by
  rw [ordNormalization_chain_identity, hc, map_zero, zero_add]

end FiniteChains.Comb
