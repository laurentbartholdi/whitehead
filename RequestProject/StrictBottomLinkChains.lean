module

public import RequestProject.StrictTopLinkCoefficients
public import RequestProject.PosetCoverLowerInterval
public import RequestProject.OrderNerveRealizationPosetCover

@[expose] public section

/-! The actual upper link of a minimal vertex, including relative boundaries.

This is the bottom-vertex counterpart of `StrictTopLinkChains`.  In particular,
the two-chain need not be a cycle: its boundary only has to vanish on edges
starting at the selected vertex.
-/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def StrictAbove (v : P) := {p : P // v < p}

instance (v : P) : PartialOrder (StrictAbove v) := Subtype.partialOrder _

noncomputable def strictSourceRayEdge (v : P) (e : StrictOrdEdge P) :
    StrictAbove v →₀ ℤ := by
  classical
  exact if h : e.1.1 = v then Finsupp.single ⟨e.1.2, h ▸ e.2⟩ 1 else 0

noncomputable def strictSourceRayChain (v : P) :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (StrictAbove v →₀ ℤ) :=
  Finsupp.linearCombination ℤ (strictSourceRayEdge v)

noncomputable def strictBottomLinkTriangle (v : P) (t : StrictOrdTri P) :
    StrictOrdEdge (StrictAbove v) →₀ ℤ := by
  classical
  exact if h : t.1.1 = v then Finsupp.single
    ⟨(⟨t.1.2.1, h ▸ t.2.1⟩, ⟨t.1.2.2, h ▸ t.2.1.trans t.2.2⟩), t.2.2⟩ 1 else 0

noncomputable def strictBottomLinkChain (v : P) :
    (StrictOrdTri P →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge (StrictAbove v) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (strictBottomLinkTriangle v)

def strictBottomConeTriangle (v : P) (e : StrictOrdEdge (StrictAbove v)) :
    StrictOrdTri P :=
  ⟨(v, e.1.1.val, e.1.2.val), e.1.1.property, e.2⟩

theorem strictBottomLinkChain_apply (v : P) (c : StrictOrdTri P →₀ ℤ)
    (e : StrictOrdEdge (StrictAbove v)) :
    strictBottomLinkChain v c e = c (strictBottomConeTriangle v e) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]
  | single t n =>
    rcases t with ⟨⟨z, a, b⟩, hza, hab⟩
    rcases e with ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hxy⟩
    by_cases ht : z = v
    · subst z
      simp [strictBottomLinkChain, strictBottomLinkTriangle, strictBottomConeTriangle,
        Finsupp.single_apply, StrictOrdTri, StrictOrdEdge, StrictAbove,
        Subtype.mk.injEq, Prod.mk.injEq]
    · simp [strictBottomLinkChain, strictBottomLinkTriangle, ht, strictBottomConeTriangle,
        StrictOrdTri, StrictOrdEdge, StrictAbove]

theorem strictSourceRayChain_apply (v : P) (c : StrictOrdEdge P →₀ ℤ)
    (x : StrictAbove v) :
    strictSourceRayChain v c x = c ⟨(v, x.val), x.property⟩ := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]
  | single e n =>
    rcases e with ⟨⟨a, b⟩, hab⟩
    rcases x with ⟨x, hx⟩
    by_cases ha : a = v
    · subst a
      simp [strictSourceRayChain, strictSourceRayEdge, Finsupp.single_apply,
        StrictOrdEdge, StrictAbove, Subtype.mk.injEq, Prod.mk.injEq]
    · simp [strictSourceRayChain, strictSourceRayEdge, ha, StrictOrdEdge, StrictAbove]

/-- At a minimal vertex the extracted upper link has the negative source-ray
boundary.  This identity applies to every finite chain, including relative chains. -/
theorem strictBottomLink_boundary (v : P) (hm : ∀ p, p ≤ v → p = v)
    (c : StrictOrdTri P →₀ ℤ) :
    bdry1 (strictOrderCx (StrictAbove v)) (strictBottomLinkChain v c) =
      -strictSourceRayChain v (bdry2 (strictOrderCx P) c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd, neg_add]
  | single t n =>
    have hmid : t.1.2.1 ≠ v := by
      intro he
      have ht := hm t.1.1 (he ▸ t.2.1.le)
      exact (ne_of_lt t.2.1) (ht.trans he.symm)
    rw (config := { transparency := .default }) [strictTriangle_bdry2_single, map_sub, map_add]
    by_cases ht : t.1.1 = v
    · simp [strictSourceRayChain, strictSourceRayEdge, strictBottomLinkChain,
        strictBottomLinkTriangle, strictTriangleEdge01, strictTriangleEdge12,
        strictTriangleEdge02, hmid, ht, bdry1, strictOrderCx, smul_sub,
        neg_sub]
    · simp [strictSourceRayChain, strictSourceRayEdge, strictBottomLinkChain,
        strictBottomLinkTriangle, strictTriangleEdge01, strictTriangleEdge12,
        strictTriangleEdge02, hmid, ht]

/-- Only source-edge boundary vanishing is used; no absolute cycle premise is
introduced when extracting the link of a relative two-chain. -/
theorem strictBottomLink_relative_cycle (v : P) (hm : ∀ p, p ≤ v → p = v)
    (c : StrictOrdTri P →₀ ℤ)
    (hc : ∀ e : StrictOrdEdge P, e.1.1 = v → bdry2 (strictOrderCx P) c e = 0) :
    bdry1 (strictOrderCx (StrictAbove v)) (strictBottomLinkChain v c) = 0 := by
  rw (config := { transparency := .default }) [strictBottomLink_boundary v hm]
  have hz : strictSourceRayChain v (bdry2 (strictOrderCx P) c) = 0 := by
    ext x
    rw (config := { transparency := .default }) [strictSourceRayChain_apply]
    exact hc _ rfl
  rw (config := { transparency := .default }) [hz, neg_zero]

namespace IsPosetCover
variable {Q : Type u} [PartialOrder Q] {f : P → Q} (hf : IsPosetCover f)

include hf in
theorem upperInterval_le_reflect {a b v : P} (ha : v ≤ a) (hb : v ≤ b)
    (h : f a ≤ f b) : a ≤ b := by
  obtain ⟨c, ⟨hac, hfc⟩, _⟩ := hf.up a (f b) h
  have hc : c = b := hf.up_inj (ha.trans hac) hb hfc
  exact hc ▸ hac

noncomputable def upperIntervalLift (v : P) (q : StrictAbove (f v)) :
    StrictAbove v := by
  let a := Classical.choose (hf.up v q.1 q.2.le)
  have hs : v ≤ a ∧ f a = q.1 := (Classical.choose_spec (hf.up v q.1 q.2.le)).1
  exact ⟨a, lt_of_le_of_ne hs.1 (by
    intro he
    exact (ne_of_lt q.2) ((congrArg f he).trans hs.2))⟩

theorem upperIntervalLift_projection (v : P) (q : StrictAbove (f v)) :
    f (hf.upperIntervalLift v q).1 = q.1 :=
  (Classical.choose_spec (hf.up v q.1 q.2.le)).1.2

/-- An actual cover identifies each upper link with the actual upper link in
the base.  Distinct pole lifts are not identified by this construction. -/
noncomputable def upperIntervalOrderIso (v : P) :
    StrictAbove v ≃o StrictAbove (f v) where
  toFun p := ⟨f p.1, hf.strictMono p.2⟩
  invFun := hf.upperIntervalLift v
  left_inv p := Subtype.ext (hf.up_inj (hf.upperIntervalLift v _).2.le p.2.le
    (hf.upperIntervalLift_projection v _))
  right_inv q := Subtype.ext (hf.upperIntervalLift_projection v q)
  map_rel_iff' {a b} := ⟨fun h => upperInterval_le_reflect hf a.2.le b.2.le h,
    fun h => hf.mono h⟩

end IsPosetCover

def strictAboveCongr {a b : P} (h : a = b) : StrictAbove a ≃o StrictAbove b := by
  cases h
  exact OrderIso.refl _

theorem strictAboveCongr_val {a b : P} (h : a = b) (x : StrictAbove a) :
    (strictAboveCongr h x).val = x.val := by
  cases h
  rfl

end FiniteChains.Comb
