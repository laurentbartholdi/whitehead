import RequestProject.StrictOrderChains

/-! Explicit one-cycle fillings for a downward componentwise collapse. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]
  (g : P → P) (hle : ∀ x, g x ≤ x)

def downwardEdgeTriangle (e : StrictOrdEdge P) : OrdTri P :=
  ⟨(g e.1.1, e.1.1, e.1.2), hle _, e.2.le⟩

noncomputable def downwardEdgeFan : (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (StrictOrdTri P →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun e => normalizeOrdTriangle (downwardEdgeTriangle g hle e))

noncomputable def downwardRadialChain : (P →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge P →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => normalizeOrdEdge ⟨(g x, x), hle x⟩)

theorem downwardEdgeTriangle_boundary (he : ∀ {a b : P}, a ≤ b → g a = g b)
    (e : StrictOrdEdge P) :
    bdry2 (strictOrderCx P) (normalizeOrdTriangle (downwardEdgeTriangle g hle e)) =
      Finsupp.single e 1 + normalizeOrdEdge ⟨(g e.1.1, e.1.1), hle _⟩ -
        normalizeOrdEdge ⟨(g e.1.2, e.1.2), hle _⟩ := by
  have h := bdry2_normalizeOrdChain2 (Finsupp.single (downwardEdgeTriangle g hle e) (1 : ℤ))
  have hs : normalizeOrdEdge ⟨e.1, e.2.le⟩ = Finsupp.single e (1 : ℤ) := by
    simp [normalizeOrdEdge, e.2.ne]
  have hr : normalizeOrdEdge ⟨(g e.1.1, e.1.2), (hle _).trans e.2.le⟩ =
      normalizeOrdEdge ⟨(g e.1.2, e.1.2), hle _⟩ := by
    congr 1
    exact Subtype.ext (Prod.ext (he e.2.le) rfl)
  rw [normalizeOrdChain2_single, one_smul, Comb.bdry2_single, one_smul] at h
  simp [downwardEdgeTriangle, orderCx, pathChain] at h
  rw [hs, hr] at h
  dsimp only [downwardEdgeTriangle]
  rw [h]
  abel

theorem downwardEdgeFan_boundary (he : ∀ {a b : P}, a ≤ b → g a = g b)
    (c : StrictOrdEdge P →₀ ℤ) :
    bdry2 (strictOrderCx P) (downwardEdgeFan g hle c) =
      c - downwardRadialChain g hle (bdry1 (strictOrderCx P) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, map_add]; abel
  | single e n =>
    rw [downwardEdgeFan, Finsupp.linearCombination_single, map_smul,
      downwardEdgeTriangle_boundary g hle he, bdry1_single]
    simp [downwardRadialChain, strictOrderCx, smul_add, smul_sub]
    abel

/-- All strict one-cycles have explicit finite strict triangle fillings. -/
theorem downwardEdgeFan_cycle_boundary (he : ∀ {a b : P}, a ≤ b → g a = g b)
    (c : StrictOrdEdge P →₀ ℤ) (hc : bdry1 (strictOrderCx P) c = 0) :
    bdry2 (strictOrderCx P) (downwardEdgeFan g hle c) = c := by
  rw [downwardEdgeFan_boundary g hle he, hc, map_zero, sub_zero]

end FiniteChains.Comb
