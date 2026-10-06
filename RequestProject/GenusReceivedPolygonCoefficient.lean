module

public import RequestProject.StrictBottomLinkChains
public import RequestProject.SurfaceLink
public import RequestProject.GenusSurface
public import RequestProject.GenusCellularFundamental
public import RequestProject.CellularChainMapZero

@[expose] public section

/-! Pole coefficients in genuine covers of the polygon surface.

The coefficients here are indexed by actual lifts of the polygon centre.  No
augmentation, connected-cover premise, or faithfulness of a group receiver is
used.  The input is a relative two-chain: its boundary vanishes on edges over
the polygon centre, as it does when supported on the marked boundary graph.

This file extracts and reconstructs the part incident to the centre.  Extension
of this rigidity through the six flags of each inner triangle and through the
collar, and its transport from the attaching barycentric cover, remain separate
dependencies of the full B2 proof.
-/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open Comb Cell
universe u
variable {κ ι : Type u} {M : ℕ} [NeZero M]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)

abbrev PolygonPoleLink := StrictAbove (cC hc)

def polygonPoleRadius (p : Fin M) : PolygonPoleLink hc :=
  ⟨cR hc p, ctr_lt_rad hc p⟩

def polygonPoleTriangle (p : Fin M) : PolygonPoleLink hc :=
  ⟨cI hc p, ctr_lt_inn hc p⟩

def polygonPoleEdgePlus (p : Fin M) : StrictOrdEdge (PolygonPoleLink hc) :=
  ⟨(polygonPoleRadius hc p, polygonPoleTriangle hc p),
    (lt_inn_iff hc).2 (Or.inr (Or.inl rfl))⟩

def polygonPoleEdgeMinus (p : Fin M) : StrictOrdEdge (PolygonPoleLink hc) :=
  ⟨(polygonPoleRadius hc (p + 1), polygonPoleTriangle hc p),
    (lt_inn_iff hc).2 (Or.inr (Or.inr (Or.inl rfl)))⟩

/-- All edges of the actual upper link are the two radial incidences of an
actual inner triangle; no presentation of the link is assumed. -/
theorem polygonPoleLink_edge_cases (e : StrictOrdEdge (PolygonPoleLink hc)) :
    ∃ p : Fin M, e = polygonPoleEdgePlus hc p ∨ e = polygonPoleEdgeMinus hc p := by
  rcases e with ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hab⟩
  change toS vc ec hc ctr < toS vc ec hc a at ha
  change toS vc ec hc a < toS vc ec hc b at hab
  obtain ⟨p, hp | hp⟩ := (ctr_lt_iff hc).mp ha
  · subst a
    rcases (rad_lt_iff hc).mp hab with hb' | hb'
    · subst b
      exact ⟨p, Or.inl rfl⟩
    · subst b
      refine ⟨fpred p, Or.inr ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        simp only [polygonPoleEdgeMinus, polygonPoleRadius, cR, toS, fpred_add_one]
      · rfl
  · subst a
    have hh := (lt_iff_plt hc).mp hab
    cases b <;> simp [plt] at hh

@[simp] theorem polygonPoleRadius_eq_iff (p r : Fin M) :
    polygonPoleRadius hc p = polygonPoleRadius hc r ↔ p = r := by
  constructor
  · intro h
    exact Cell.rad.inj (congrArg (fun x : PolygonPoleLink hc => x.val) h)
  · rintro rfl
    rfl

@[simp] theorem polygonPoleTriangle_eq_iff (p r : Fin M) :
    polygonPoleTriangle hc p = polygonPoleTriangle hc r ↔ p = r := by
  constructor
  · intro h
    exact Cell.inn.inj (congrArg (fun x : PolygonPoleLink hc => x.val) h)
  · rintro rfl
    rfl

@[simp] theorem polygonPoleRadius_ne_triangle (p r : Fin M) :
    polygonPoleRadius hc p ≠ polygonPoleTriangle hc r := by
  intro he
  have hh := congrArg Subtype.val he
  cases hh

@[simp] theorem polygonPoleTriangle_ne_radius (p r : Fin M) :
    polygonPoleTriangle hc p ≠ polygonPoleRadius hc r :=
  (polygonPoleRadius_ne_triangle hc r p).symm

@[simp] theorem polygonPoleEdgePlus_eq_iff (p r : Fin M) :
    polygonPoleEdgePlus hc p = polygonPoleEdgePlus hc r ↔ p = r := by
  constructor
  · intro he
    exact (polygonPoleTriangle_eq_iff hc p r).mp
      (congrArg (fun e : StrictOrdEdge (PolygonPoleLink hc) => e.1.2) he)
  · rintro rfl
    rfl

@[simp] theorem polygonPoleEdgeMinus_eq_iff (p r : Fin M) :
    polygonPoleEdgeMinus hc p = polygonPoleEdgeMinus hc r ↔ p = r := by
  constructor
  · intro he
    exact (polygonPoleTriangle_eq_iff hc p r).mp
      (congrArg (fun e : StrictOrdEdge (PolygonPoleLink hc) => e.1.2) he)
  · rintro rfl
    rfl

theorem polygonPoleEdgePlus_ne_minus (hM : 2 ≤ M) (p r : Fin M) :
    polygonPoleEdgePlus hc p ≠ polygonPoleEdgeMinus hc r := by
  intro he
  have hpr : p = r := (polygonPoleTriangle_eq_iff hc p r).mp
    (congrArg (fun e : StrictOrdEdge (PolygonPoleLink hc) => e.1.2) he)
  subst r
  have hr : p = p + 1 := (polygonPoleRadius_eq_iff hc p (p + 1)).mp
    (congrArg (fun e : StrictOrdEdge (PolygonPoleLink hc) => e.1.1) he)
  exact fin_succ_ne_self hM p hr.symm

/-- The two actual incidences at an inner-triangle vertex have their genuine
positive boundary signs. -/
theorem polygonPole_boundary_triangle (hM : 2 ≤ M)
    (d : StrictOrdEdge (PolygonPoleLink hc) →₀ ℤ) (p : Fin M) :
    Comb.bdry1 (strictOrderCx (PolygonPoleLink hc)) d (polygonPoleTriangle hc p) =
      d (polygonPoleEdgePlus hc p) + d (polygonPoleEdgeMinus hc p) := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => simp only [map_add, Finsupp.add_apply, hd, he]; ring
  | single e n =>
    obtain ⟨r, hr | hr⟩ := polygonPoleLink_edge_cases hc e
    · subst e
      rw (config := { transparency := .default }) [Comb.bdry1_single]
      change (n • (Finsupp.single (polygonPoleTriangle hc r) (1 : ℤ) -
        Finsupp.single (polygonPoleRadius hc r) 1) : PolygonPoleLink hc →₀ ℤ) _ = _
      simp [Finsupp.single_apply, polygonPoleEdgePlus_ne_minus hc hM]
    · subst e
      have hne := fun r p => (polygonPoleEdgePlus_ne_minus hc hM p r).symm
      rw (config := { transparency := .default }) [Comb.bdry1_single]
      change (n • (Finsupp.single (polygonPoleTriangle hc r) (1 : ℤ) -
        Finsupp.single (polygonPoleRadius hc (r + 1)) 1) : PolygonPoleLink hc →₀ ℤ) _ = _
      simp [Finsupp.single_apply, hne]

/-- At a radius, the two actual incidences have their genuine negative signs. -/
theorem polygonPole_boundary_radius (hM : 2 ≤ M)
    (d : StrictOrdEdge (PolygonPoleLink hc) →₀ ℤ) (p : Fin M) :
    Comb.bdry1 (strictOrderCx (PolygonPoleLink hc)) d (polygonPoleRadius hc (p + 1)) =
      -d (polygonPoleEdgePlus hc (p + 1)) - d (polygonPoleEdgeMinus hc p) := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => simp only [map_add, Finsupp.add_apply, hd, he]; ring
  | single e n =>
    obtain ⟨r, hr | hr⟩ := polygonPoleLink_edge_cases hc e
    · subst e
      rw (config := { transparency := .default }) [Comb.bdry1_single]
      change (n • (Finsupp.single (polygonPoleTriangle hc r) (1 : ℤ) -
        Finsupp.single (polygonPoleRadius hc r) 1) : PolygonPoleLink hc →₀ ℤ) _ = _
      simp [Finsupp.single_apply, polygonPoleEdgePlus_ne_minus hc hM]
    · subst e
      have hne := fun r p => (polygonPoleEdgePlus_ne_minus hc hM p r).symm
      rw (config := { transparency := .default }) [Comb.bdry1_single]
      change (n • (Finsupp.single (polygonPoleTriangle hc r) (1 : ℤ) -
        Finsupp.single (polygonPoleRadius hc (r + 1)) 1) : PolygonPoleLink hc →₀ ℤ) _ = _
      simp [Finsupp.single_apply, hne]

/-- Every integral one-cycle of the actual polygon-centre link has a single
coefficient.  This is the local coefficient rigidity used at each cover pole. -/
theorem polygonPole_cycle_coefficients (hM : 2 ≤ M)
    (d : StrictOrdEdge (PolygonPoleLink hc) →₀ ℤ)
    (hd : Comb.bdry1 (strictOrderCx (PolygonPoleLink hc)) d = 0) (p : Fin M) :
    d (polygonPoleEdgePlus hc p) = d (polygonPoleEdgePlus hc 0) ∧
      d (polygonPoleEdgeMinus hc p) = -d (polygonPoleEdgePlus hc 0) := by
  have hlocal (r : Fin M) :
      d (polygonPoleEdgeMinus hc r) = -d (polygonPoleEdgePlus hc r) ∧
      d (polygonPoleEdgePlus hc (r + 1)) = d (polygonPoleEdgePlus hc r) := by
    have ht := polygonPole_boundary_triangle hc hM d r
    have hr := polygonPole_boundary_radius hc hM d r
    rw (config := { transparency := .default }) [hd, Finsupp.zero_apply] at ht hr
    omega
  have hall : ∀ n (hn : n < M),
      d (polygonPoleEdgePlus hc ⟨n, hn⟩) = d (polygonPoleEdgePlus hc 0) := by
    intro n
    induction n with
    | zero => intro hn; rfl
    | succ n ih =>
      intro hn
      have hp : n < M := by omega
      have hs : (⟨n, hp⟩ : Fin M) + 1 = ⟨n + 1, hn⟩ := by
        apply Fin.ext
        rw (config := { transparency := .default }) [fin_succ_val]
        exact Nat.mod_eq_of_lt hn
      rw (config := { transparency := .default }) [← hs, (hlocal ⟨n, hp⟩).2]
      exact ih hp
  have he := hall p.val p.isLt
  exact ⟨he, (hlocal p).1.trans (congrArg Neg.neg he)⟩

/-- Agreement at one actual radial incidence determines the entire pole link. -/
theorem polygonPole_cycle_ext (hM : 2 ≤ M)
    (c d : StrictOrdEdge (PolygonPoleLink hc) →₀ ℤ)
    (hc' : Comb.bdry1 (strictOrderCx (PolygonPoleLink hc)) c = 0)
    (hd : Comb.bdry1 (strictOrderCx (PolygonPoleLink hc)) d = 0)
    (he : c (polygonPoleEdgePlus hc 0) = d (polygonPoleEdgePlus hc 0)) : c = d := by
  ext e
  obtain ⟨p, hp | hp⟩ := polygonPoleLink_edge_cases hc e
  · subst e
    exact (polygonPole_cycle_coefficients hc hM c hc' p).1.trans
      (he.trans (polygonPole_cycle_coefficients hc hM d hd p).1.symm)
  · subst e
    exact (polygonPole_cycle_coefficients hc hM c hc' p).2.trans
      ((congrArg Neg.neg he).trans (polygonPole_cycle_coefficients hc hM d hd p).2.symm)

/-- The actual oriented radial circle of the polygon fan. -/
noncomputable def polygonPoleFundamentalLink : StrictOrdEdge (PolygonPoleLink hc) →₀ ℤ :=
  ∑ p : Fin M,
    (Finsupp.single (polygonPoleEdgePlus hc p) 1 -
      Finsupp.single (polygonPoleEdgeMinus hc p) 1)

theorem polygonPoleFundamentalLink_plus (hM : 2 ≤ M) (p : Fin M) :
    polygonPoleFundamentalLink hc (polygonPoleEdgePlus hc p) = 1 := by
  classical
  have hne := fun r p => (polygonPoleEdgePlus_ne_minus hc hM p r).symm
  simp [polygonPoleFundamentalLink,
    Finsupp.single_apply, hne]

theorem polygonPoleFundamentalLink_minus (hM : 2 ≤ M) (p : Fin M) :
    polygonPoleFundamentalLink hc (polygonPoleEdgeMinus hc p) = -1 := by
  classical
  simp [polygonPoleFundamentalLink,
    Finsupp.single_apply, polygonPoleEdgePlus_ne_minus hc hM]

/-- Every actual radial-circle cycle is the multiple of the actual oriented
circle determined by one of its coefficients. -/
theorem polygonPole_cycle_eq_multiple (hM : 2 ≤ M)
    (d : StrictOrdEdge (PolygonPoleLink hc) →₀ ℤ)
    (hd : Comb.bdry1 (strictOrderCx (PolygonPoleLink hc)) d = 0) :
    d = d (polygonPoleEdgePlus hc 0) • polygonPoleFundamentalLink hc := by
  ext e
  obtain ⟨p, hp | hp⟩ := polygonPoleLink_edge_cases hc e
  · subst e
    rw (config := { transparency := .default }) [Finsupp.smul_apply, polygonPoleFundamentalLink_plus hc hM, smul_eq_mul, mul_one]
    exact (polygonPole_cycle_coefficients hc hM d hd p).1
  · subst e
    rw (config := { transparency := .default }) [Finsupp.smul_apply, polygonPoleFundamentalLink_minus hc hM, smul_eq_mul, mul_neg_one]
    exact (polygonPole_cycle_coefficients hc hM d hd p).2

section Cover
variable {P : Type u} [PartialOrder P] (f : P → SCell vc ec hc)
  (hf : IsPosetCover f)

theorem polygonCentre_minimal (a : SCell vc ec hc) (ha : a ≤ cC hc) : a = cC hc := by
  change a = cC hc ∨ plt vc ec a ctr at ha
  rcases ha with ha | ha
  · exact ha
  · cases a <;> simp [plt] at ha

include hf in
theorem polygonCoverPole_minimal (v : P) (hv : f v = cC hc) :
    ∀ a, a ≤ v → a = v := by
  intro a ha
  have hfa := hf.mono ha
  rw (config := { transparency := .default }) [hv] at hfa
  exact hf.down_inj ha (le_refl v) ((polygonCentre_minimal hc (f a) hfa).trans hv.symm)

/-- The actual upper link at each genuine lifted polygon centre. -/
noncomputable def polygonCoverPoleOrderIso (v : P) (hv : f v = cC hc) :
    StrictAbove v ≃o PolygonPoleLink hc :=
  (hf.upperIntervalOrderIso v).trans (strictAboveCongr hv)

theorem polygonCoverPoleOrderIso_apply_val (v : P) (hv : f v = cC hc)
    (x : StrictAbove v) :
    (polygonCoverPoleOrderIso hc f hf v hv x).val = f x.val := by
  change (strictAboveCongr hv (hf.upperIntervalOrderIso v x)).val = f x.val
  rw (config := { transparency := .default }) [strictAboveCongr_val]
  rfl

noncomputable def polygonCoverPoleHom (v : P) (hv : f v = cC hc) :
    Hom (strictOrderCx (StrictAbove v)) (strictOrderCx (PolygonPoleLink hc)) :=
  strictOrderCxMap (polygonCoverPoleOrderIso hc f hf v hv)
    (polygonCoverPoleOrderIso hc f hf v hv).strictMono

noncomputable def polygonCoverPoleLink (v : P) (hv : f v = cC hc)
    (c : StrictOrdTri P →₀ ℤ) : StrictOrdEdge (PolygonPoleLink hc) →₀ ℤ :=
  chain1 (polygonCoverPoleHom hc f hf v hv) (strictBottomLinkChain v c)

/-- A relative chain with boundary on the marked boundary graph gives a cycle
at each lifted pole.  The two-chain itself is not assumed closed. -/
theorem polygonCoverPoleLink_cycle (v : P) (hv : f v = cC hc)
    (c : StrictOrdTri P →₀ ℤ)
    (hrel : ∀ e : StrictOrdEdge P,
      f e.1.1 = cC hc → Comb.bdry2 (strictOrderCx P) c e = 0) :
    Comb.bdry1 (strictOrderCx (PolygonPoleLink hc))
      (polygonCoverPoleLink hc f hf v hv c) = 0 := by
  change Comb.bdry1 _ (chain1 (polygonCoverPoleHom hc f hf v hv)
    (strictBottomLinkChain v c)) = 0
  rw (config := { transparency := .default }) [bdry1_chain1]
  have hlink := strictBottomLink_relative_cycle v
    (polygonCoverPole_minimal hc f hf v hv) c (fun e he => hrel e (he.symm ▸ hv))
  rw (config := { transparency := .default }) [hlink, map_zero]

/-- Projection within one lifted upper interval keeps every actual coefficient. -/
theorem polygonCoverPoleLink_apply (v : P) (hv : f v = cC hc)
    (c : StrictOrdTri P →₀ ℤ) (e : StrictOrdEdge (StrictAbove v)) :
    polygonCoverPoleLink hc f hf v hv c
      ((polygonCoverPoleHom hc f hf v hv).onE e) =
        c (strictBottomConeTriangle v e) :=
  (strictOrderCxMap_chain1_apply
    (polygonCoverPoleOrderIso hc f hf v hv)
    (polygonCoverPoleOrderIso hc f hf v hv).strictMono
    (polygonCoverPoleOrderIso hc f hf v hv).injective
    (strictBottomLinkChain v c) e).trans (strictBottomLinkChain_apply v c e)

noncomputable def polygonCoverPoleFlagPlus (v : P) (hv : f v = cC hc)
    (p : Fin M) : StrictOrdTri P :=
  strictBottomConeTriangle v
    ((strictOrderEdgeEquiv (polygonCoverPoleOrderIso hc f hf v hv)).symm
      (polygonPoleEdgePlus hc p))

noncomputable def polygonCoverPoleFlagMinus (v : P) (hv : f v = cC hc)
    (p : Fin M) : StrictOrdTri P :=
  strictBottomConeTriangle v
    ((strictOrderEdgeEquiv (polygonCoverPoleOrderIso hc f hf v hv)).symm
      (polygonPoleEdgeMinus hc p))

theorem polygonCoverPoleFlagPlus_projection (v : P) (hv : f v = cC hc) (p : Fin M) :
    f (polygonCoverPoleFlagPlus hc f hf v hv p).1.1 = cC hc ∧
    f (polygonCoverPoleFlagPlus hc f hf v hv p).1.2.1 = cR hc p ∧
    f (polygonCoverPoleFlagPlus hc f hf v hv p).1.2.2 = cI hc p := by
  let iso := polygonCoverPoleOrderIso hc f hf v hv
  let eqv := strictOrderEdgeEquiv iso
  let e := eqv.symm (polygonPoleEdgePlus hc p)
  have he : eqv e = polygonPoleEdgePlus hc p := eqv.apply_symm_apply _
  have h₁ := congrArg (fun z : StrictOrdEdge (PolygonPoleLink hc) => z.1.1.val) he
  have h₂ := congrArg (fun z : StrictOrdEdge (PolygonPoleLink hc) => z.1.2.val) he
  change (iso e.1.1).val = cR hc p at h₁
  change (iso e.1.2).val = cI hc p at h₂
  rw (config := { transparency := .default }) [polygonCoverPoleOrderIso_apply_val] at h₁ h₂
  exact ⟨hv, h₁, h₂⟩

theorem polygonCoverPoleLink_plus (v : P) (hv : f v = cC hc)
    (c : StrictOrdTri P →₀ ℤ) (p : Fin M) :
    polygonCoverPoleLink hc f hf v hv c (polygonPoleEdgePlus hc p) =
      c (polygonCoverPoleFlagPlus hc f hf v hv p) := by
  let e := strictOrderEdgeEquiv (polygonCoverPoleOrderIso hc f hf v hv)
  have hh := polygonCoverPoleLink_apply hc f hf v hv c
    (e.symm (polygonPoleEdgePlus hc p))
  change polygonCoverPoleLink hc f hf v hv c
    (e (e.symm (polygonPoleEdgePlus hc p))) = _ at hh
  rw (config := { transparency := .default }) [e.apply_symm_apply] at hh
  exact hh

theorem polygonCoverPoleLink_minus (v : P) (hv : f v = cC hc)
    (c : StrictOrdTri P →₀ ℤ) (p : Fin M) :
    polygonCoverPoleLink hc f hf v hv c (polygonPoleEdgeMinus hc p) =
      c (polygonCoverPoleFlagMinus hc f hf v hv p) := by
  let e := strictOrderEdgeEquiv (polygonCoverPoleOrderIso hc f hf v hv)
  have hh := polygonCoverPoleLink_apply hc f hf v hv c
    (e.symm (polygonPoleEdgeMinus hc p))
  change polygonCoverPoleLink hc f hf v hv c
    (e (e.symm (polygonPoleEdgeMinus hc p))) = _ at hh
  rw (config := { transparency := .default }) [e.apply_symm_apply] at hh
  exact hh

/-- The actual finite set of nonzero coefficients is indexed by actual pole
lifts, even for disconnected covers with arbitrarily many sheets. -/
abbrev PolygonCoverPole := {v : P // f v = cC hc}

noncomputable def polygonCoverPoleFlag (v : PolygonCoverPole hc f) : StrictOrdTri P :=
  polygonCoverPoleFlagPlus hc f hf v.1 v.2 0

theorem polygonCoverPoleFlag_injective :
    Function.Injective (polygonCoverPoleFlag hc f hf) := by
  intro v w h
  apply Subtype.ext
  exact congrArg (fun t : StrictOrdTri P => t.1.1) h

noncomputable def polygonCoverPoleCoefficients :
    (StrictOrdTri P →₀ ℤ) →ₗ[ℤ] (PolygonCoverPole hc f →₀ ℤ) :=
  (Finsupp.comapDomain.addMonoidHom (polygonCoverPoleFlag_injective hc f hf)).toIntLinearMap

theorem polygonCoverPoleCoefficients_apply (c : StrictOrdTri P →₀ ℤ)
    (v : PolygonCoverPole hc f) :
    polygonCoverPoleCoefficients hc f hf c v = c (polygonCoverPoleFlag hc f hf v) := rfl

/-- One actual lifted flag coefficient determines every radial flag in its
polygon fan, with the orientation of the genuine fundamental filling. -/
theorem polygonCoverPole_coefficients (hM : 2 ≤ M)
    (c : StrictOrdTri P →₀ ℤ)
    (hrel : ∀ e : StrictOrdEdge P,
      f e.1.1 = cC hc → Comb.bdry2 (strictOrderCx P) c e = 0)
    (v : PolygonCoverPole hc f) (p : Fin M) :
    c (polygonCoverPoleFlagPlus hc f hf v.1 v.2 p) =
        polygonCoverPoleCoefficients hc f hf c v ∧
      c (polygonCoverPoleFlagMinus hc f hf v.1 v.2 p) =
        -polygonCoverPoleCoefficients hc f hf c v := by
  have hh := polygonPole_cycle_coefficients hc hM
    (polygonCoverPoleLink hc f hf v.1 v.2 c)
    (polygonCoverPoleLink_cycle hc f hf v.1 v.2 c hrel) p
  simpa only [polygonCoverPoleLink_plus, polygonCoverPoleLink_minus,
    polygonCoverPoleCoefficients_apply, polygonCoverPoleFlag] using hh

/-- The extracted link of each actual polygon lift is a scalar multiple of
the actual radial circle, with the scalar read from the original two-chain. -/
theorem polygonCoverPoleLink_eq_multiple (hM : 2 ≤ M)
    (c : StrictOrdTri P →₀ ℤ)
    (hrel : ∀ e : StrictOrdEdge P,
      f e.1.1 = cC hc → Comb.bdry2 (strictOrderCx P) c e = 0)
    (v : PolygonCoverPole hc f) :
    polygonCoverPoleLink hc f hf v.1 v.2 c =
      polygonCoverPoleCoefficients hc f hf c v • polygonPoleFundamentalLink hc := by
  have hh := polygonPole_cycle_eq_multiple hc hM
    (polygonCoverPoleLink hc f hf v.1 v.2 c)
    (polygonCoverPoleLink_cycle hc f hf v.1 v.2 c hrel)
  simpa only [polygonCoverPoleLink_plus, polygonCoverPoleCoefficients_apply,
    polygonCoverPoleFlag] using hh

/-- Equality of the finitely supported pole coefficients forces equality on
every actual triangle incident to a pole.  This is relative coefficient
rigidity in a genuine cover, rather than an augmented statement on the base. -/
theorem polygonCoverPole_relative_ext (hM : 2 ≤ M)
    (c d : StrictOrdTri P →₀ ℤ)
    (hc' : ∀ e : StrictOrdEdge P,
      f e.1.1 = cC hc → Comb.bdry2 (strictOrderCx P) c e = 0)
    (hd : ∀ e : StrictOrdEdge P,
      f e.1.1 = cC hc → Comb.bdry2 (strictOrderCx P) d e = 0)
    (he : polygonCoverPoleCoefficients hc f hf c = polygonCoverPoleCoefficients hc f hf d)
    (t : StrictOrdTri P) (ht : f t.1.1 = cC hc) : c t = d t := by
  let v : PolygonCoverPole hc f := ⟨t.1.1, ht⟩
  have hp : c (polygonCoverPoleFlag hc f hf v) = d (polygonCoverPoleFlag hc f hf v) :=
    congrArg (fun z => z v) he
  have hlink := polygonPole_cycle_ext hc hM
    (polygonCoverPoleLink hc f hf v.1 v.2 c)
    (polygonCoverPoleLink hc f hf v.1 v.2 d)
    (polygonCoverPoleLink_cycle hc f hf v.1 v.2 c hc')
    (polygonCoverPoleLink_cycle hc f hf v.1 v.2 d hd)
    (by simpa only [polygonCoverPoleLink_plus, polygonCoverPoleFlag] using hp)
  let e : StrictOrdEdge (StrictAbove v.1) :=
    ⟨(⟨t.1.2.1, t.2.1⟩, ⟨t.1.2.2, t.2.1.trans t.2.2⟩), t.2.2⟩
  have hh := congrArg (fun z => z ((polygonCoverPoleHom hc f hf v.1 v.2).onE e)) hlink
  convert hh using 1 <;> simp only [polygonCoverPoleLink_apply] <;> rfl

/-- Reindexing the genuine pole lifts by a group gives a full group-ring
coefficient.  The next formula shows explicitly that no sheet is summed away. -/
noncomputable def polygonCoverGroupCoefficient {G : Type u} [Group G]
    (e : PolygonCoverPole hc f ≃ G) (c : StrictOrdTri P →₀ ℤ) : MonoidAlgebra ℤ G :=
  MonoidAlgebra.ofCoeff (Finsupp.mapDomain e (polygonCoverPoleCoefficients hc f hf c))

theorem polygonCoverGroupCoefficient_apply {G : Type u} [Group G]
    (e : PolygonCoverPole hc f ≃ G) (c : StrictOrdTri P →₀ ℤ)
    (v : PolygonCoverPole hc f) :
    (polygonCoverGroupCoefficient hc f hf e c).coeff (e v) = c (polygonCoverPoleFlag hc f hf v) :=
  (Finsupp.mapDomain_apply_of_injective e.injective (polygonCoverPoleCoefficients hc f hf c) v).trans
    (polygonCoverPoleCoefficients_apply hc f hf c v)

end Cover

/-- The one-dimensional identified boundary of the polygon. -/
def InPolygonBoundary : SCell vc ec hc → Prop
  | .vtx _ => True
  | .bed _ => True
  | _ => False

section BoundarySupport
variable {P : Type u} [PartialOrder P] (f : P → SCell vc ec hc)
  (hf : IsPosetCover f)

/-- The relative hypothesis used above follows directly from actual boundary
support on the polygon marking, without a homology or cycle assumption. -/
theorem polygonCover_boundary_vanishes_at_poles
    (c : StrictOrdTri P →₀ ℤ)
    (hboundary : ∀ e ∈ (Comb.bdry2 (strictOrderCx P) c).support,
      InPolygonBoundary hc (f e.1.1)) :
    ∀ e : StrictOrdEdge P,
      f e.1.1 = cC hc → Comb.bdry2 (strictOrderCx P) c e = 0 := by
  intro e he
  by_contra hn
  have hh := hboundary e (Finsupp.mem_support_iff.mpr hn)
  rw (config := { transparency := .default }) [he] at hh
  exact hh

theorem polygonCoverPoleLink_eq_multiple_of_boundary_support (hM : 2 ≤ M)
    (c : StrictOrdTri P →₀ ℤ)
    (hboundary : ∀ e ∈ (Comb.bdry2 (strictOrderCx P) c).support,
      InPolygonBoundary hc (f e.1.1))
    (v : PolygonCoverPole hc f) :
    polygonCoverPoleLink hc f hf v.1 v.2 c =
      polygonCoverPoleCoefficients hc f hf c v • polygonPoleFundamentalLink hc :=
  polygonCoverPoleLink_eq_multiple hc f hf hM c
    (polygonCover_boundary_vanishes_at_poles hc f c hboundary) v

end BoundarySupport

namespace Genus
variable (q : ℕ) [NeZero q]

/-- The radial reference is exactly the upper-link chain of the already
constructed oriented genus fundamental filling, with its proved coefficient
`+1` on `genusInnerFlag`. -/
theorem genusFundamental_bottom_link :
    strictBottomLinkChain (cC (gc q)) (genusStrictFundamentalChain q) =
      polygonPoleFundamentalLink (gc q) := by
  have hM : 2 ≤ 8 * q := by
    have := Nat.pos_of_neZero q
    omega
  have hcyc : Comb.bdry1 (strictOrderCx (PolygonPoleLink (gc q)))
      (strictBottomLinkChain (cC (gc q)) (genusStrictFundamentalChain q)) = 0 := by
    apply strictBottomLink_relative_cycle _ (polygonCentre_minimal (gc q))
    intro e _
    rw (config := { transparency := .default }) [genusStrictFundamentalChain_cycle, Finsupp.zero_apply]
  have hh := polygonPole_cycle_eq_multiple (gc q) hM
    (strictBottomLinkChain (cC (gc q)) (genusStrictFundamentalChain q)) hcyc
  rw (config := { transparency := .default }) [strictBottomLinkChain_apply] at hh
  change strictBottomLinkChain (cC (gc q)) (genusStrictFundamentalChain q) =
    genusStrictFundamentalChain q (genusInnerFlag q) • polygonPoleFundamentalLink (gc q) at hh
  rw (config := { transparency := .default }) [genusStrictFundamentalChain_inner_coefficient, one_smul] at hh
  exact hh

variable {P : Type} [PartialOrder P]
  (f : P → SCell (gvc q) (gec q) (gc q)) (hf : IsPosetCover f)

/-- The genuine genus polygon has the required nondegenerate radial circle. -/
theorem genusCoverPole_coefficients
    (c : StrictOrdTri P →₀ ℤ)
    (hrel : ∀ e : StrictOrdEdge P,
      f e.1.1 = cC (gc q) → Comb.bdry2 (strictOrderCx P) c e = 0)
    (v : PolygonCoverPole (gc q) f) (p : Fin (8 * q)) :
    c (polygonCoverPoleFlagPlus (gc q) f hf v.1 v.2 p) =
        polygonCoverPoleCoefficients (gc q) f hf c v ∧
      c (polygonCoverPoleFlagMinus (gc q) f hf v.1 v.2 p) =
        -polygonCoverPoleCoefficients (gc q) f hf c v := by
  apply polygonCoverPole_coefficients (gc q) f hf _ c hrel v p
  have := Nat.pos_of_neZero q
  omega

/-- Each extracted actual pole link is a multiple of the link of the actual
genus fundamental filling.  Its scalar is the original lifted flag coefficient. -/
theorem genusCoverPoleLink_eq_fundamental_multiple
    (c : StrictOrdTri P →₀ ℤ)
    (hboundary : ∀ e ∈ (Comb.bdry2 (strictOrderCx P) c).support,
      InPolygonBoundary (gc q) (f e.1.1))
    (v : PolygonCoverPole (gc q) f) :
    polygonCoverPoleLink (gc q) f hf v.1 v.2 c =
      polygonCoverPoleCoefficients (gc q) f hf c v •
        strictBottomLinkChain (cC (gc q)) (genusStrictFundamentalChain q) := by
  rw (config := { transparency := .default }) [genusFundamental_bottom_link]
  apply polygonCoverPoleLink_eq_multiple_of_boundary_support (gc q) f hf _ c hboundary v
  have := Nat.pos_of_neZero q
  omega

end Genus
end FiniteChains.Davis
