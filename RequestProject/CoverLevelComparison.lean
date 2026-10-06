import RequestProject.ChamberAttachingJ
import RequestProject.RACGPi1Example

/-!
# Which complex is compared with which: the levels of the two models

The chamber route builds the poset of spherical cosets `FiniteChains.Davis.Sph A`, whose order
complex is the **universal** Davis complex `D`: it is simply connected
(`FiniteChains.Davis.simplyConnected_davis`).  The square complex
`FiniteChains.RACG.cubeCx A` of the project is the finite moment-angle complex `C(L)`, whose
fundamental group is `Γ = ker(W → (ℤ/2)^{L⁰})` (`FiniteChains.RACG.pi1_cubeCx_equiv`).  So the
identifications of the article are

    D = universal Davis complex,   Γ = ker(W → (ℤ/2)^S),   Γ \ D = C(L),

and a comparison of `Comb.orderCx (Sph A)` with `cubeCx A` *itself* is impossible: it must be
made with the universal cover of `cubeCx A`, the `Γ`-quotient of the order complex being what
corresponds to `cubeCx A`.

This file proves the statements that make this precise:

* `FiniteChains.Davis.pi1_orderCx_sph_trivial` — `π₁(D) = 1` for the order complex of the
  poset of spherical cosets;
* `FiniteChains.Davis.not_nonempty_pi1_equiv_cubeCx` — for the two-letter example there is
  **no** isomorphism `π₁(orderCx (Sph L)) ≃* π₁(C(L))`; the naive form of obligation A.2 is
  therefore false, and only the comparison with the universal cover can hold;
* `FiniteChains.Davis.sphAct` and its lemmas — the action of `W` on the poset of spherical
  cosets by order automorphisms, which is the deck action of the covering `D → Γ \ D`;
* `FiniteChains.Davis.sphAct_apex_eq_self_iff` — the action is free on the chambers (the
  apexes), so the quotient map is a covering on the chamber level;
* `FiniteChains.RACG.phi_surjective` and `FiniteChains.RACG.phi_eq_iff_kerPhi` — the chambers
  of `D` map onto the vertices of `C(L)`, with fibres exactly the `Γ`-orbits.

Nothing here claims the full cellular comparison `Γ \ D ≅ C(L)`; that remains open, and what is
proved is the vertex/chamber level of it together with the correction of the level mismatch.
Note also that `cubeCx A` is a *square complex*, i.e. a two-dimensional object: for `H₂`
computations the full nerve chains of `RequestProject/NervePrism.lean` (which keep `C₃` and
`∂₃`) must be used, not the two-skeleton `Comb.orderCx`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open RACG Mirror Comb

universe u

namespace RACG

variable {V : Type u} [DecidableEq V] [Fintype V] (A : CommRel V)

/-- **The parity map is onto the vertices of `C(L)`.** -/
theorem phi_surjective : Function.Surjective (phi A) := by
  classical
  intro t
  refine ⟨cword A ((Finset.univ.filter (fun s : V => t s = 1)).toList), ?_⟩
  rw [phi_cword]
  funext v
  have hcount : ((Finset.univ.filter (fun s : V => t s = 1)).toList).count v =
      if t v = 1 then 1 else 0 := by
    by_cases h : t v = 1
    · rw [if_pos h]
      rw [List.count_eq_one_of_mem (Finset.nodup_toList _)]
      simp [h]
    · rw [if_neg h]
      refine List.count_eq_zero_of_not_mem ?_
      simp [h]
  rw [parList, hcount]
  by_cases h : t v = 1
  · simp [h]
  · have : t v = 0 := by
      revert h
      generalize t v = a
      revert a
      decide
    simp [this]

omit [Fintype V] in
/-- **Two chambers give the same vertex of `C(L)` exactly when they differ by an element of
`Γ`.** -/
theorem phi_eq_iff_kerPhi (x y : CayGroup A) :
    phi A x = phi A y ↔ x⁻¹ * y ∈ kerPhi A := by
  rw [mem_kerPhi, phi_mul, phi_inv]
  constructor
  · intro h
    rw [h]
    funext v
    exact zmod2_add_self _
  · intro h
    funext v
    have h2 : phi A x v + phi A y v = 0 := congrFun h v
    revert h2
    generalize phi A x v = a
    generalize phi A y v = b
    revert a b
    decide

end RACG

namespace Davis

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

/-! ### The order complex of the poset of spherical cosets is the universal Davis complex -/

/-- **`π₁(D) = 1`.**  The order complex of the poset of spherical cosets is simply connected, so
its fundamental group is trivial at every base point. -/
theorem pi1_orderCx_sph_trivial (A : CommRel V) (p : (orderCx (Sph A)).V)
    (g : Comb.Pi1 (orderCx (Sph A)) p) : g = 1 := by
  induction g using Quotient.inductionOn with
  | h q => exact Quotient.sound (simplyConnected_davis A p q.1 q.2)

/-- **The level mismatch, refuted concretely.**  For `L` the two-point nerve, the order complex
of the poset of spherical cosets is simply connected while `C(L)` is not, so there is no
isomorphism of their fundamental groups.  Only the universal cover of `C(L)` can be compared
with the order complex. -/
theorem not_nonempty_pi1_equiv_cubeCx (p : (orderCx (Sph RACG.freeTwo)).V) :
    ¬ Nonempty (Comb.Pi1 (orderCx (Sph RACG.freeTwo)) p ≃*
      (RACG.cubeCx RACG.freeTwo).Pi1 (0 : Fin 2 → ZMod 2)) := by
  rintro ⟨e⟩
  obtain ⟨g, hg⟩ := RACG.pi1_cubeCx_nontrivial
  refine hg ?_
  have h1 : e.symm g = 1 := pi1_orderCx_sph_trivial _ p _
  have h2 := congrArg e h1
  simpa using h2

/-! ### The deck action of `W` on the poset of spherical cosets -/

omit [Fintype V] in
/-- A cell is determined by its type and the set of group elements it contains. -/
theorem le_iff_forall_inChamber {p q : Sph A} :
    p ≤ q ↔ p.spx ⊆ q.spx ∧ ∀ g : CayGroup A, InChamber g p → InChamber g q := by
  constructor
  · intro h
    refine ⟨h.1, fun g hg => ?_⟩
    have h1 : p.rep⁻¹ * g ∈ specialSub A (q.spx : Set V) :=
      specialSub_mono (by exact_mod_cast h.1) hg
    have h2 : q.rep⁻¹ * p.rep ∈ specialSub A (q.spx : Set V) := by
      have := Subgroup.inv_mem _ h.2
      rwa [mul_inv_rev, inv_inv] at this
    have h3 : q.rep⁻¹ * g = (q.rep⁻¹ * p.rep) * (p.rep⁻¹ * g) := by group
    rw [InChamber, h3]
    exact Subgroup.mul_mem _ h2 h1
  · rintro ⟨hsub, hg⟩
    have h1 : InChamber p.rep q := hg p.rep (inChamber_rep p)
    refine ⟨hsub, ?_⟩
    have := Subgroup.inv_mem _ h1
    rwa [mul_inv_rev, inv_inv] at this

/-- **The action of `W` on the poset of spherical cosets**: `x · (w W_T) = (x w) W_T`. -/
noncomputable def sphAct (x : CayGroup A) (p : Sph A) : Sph A :=
  chamberPt (x * p.rep) p.isSimplex

omit [Fintype V] in
@[simp] theorem sphAct_spx (x : CayGroup A) (p : Sph A) : (sphAct x p).spx = p.spx := rfl

omit [Fintype V] in
theorem inChamber_sphAct_self (x : CayGroup A) (p : Sph A) :
    InChamber (x * p.rep) (sphAct x p) :=
  chamberPt_inChamber _ _

omit [Fintype V] in
/-- The action is equivariant for the membership relation: `g ∈ p ↔ x g ∈ x · p`. -/
theorem inChamber_sphAct (x g : CayGroup A) (p : Sph A) :
    InChamber (x * g) (sphAct x p) ↔ InChamber g p := by
  have hq : InChamber (x * p.rep) (sphAct x p) := inChamber_sphAct_self x p
  have hq' : (x * p.rep)⁻¹ * (sphAct x p).rep ∈ specialSub A (p.spx : Set V) := by
    have := Subgroup.inv_mem _ hq
    rwa [mul_inv_rev, inv_inv] at this
  constructor
  · intro h
    have h1 : (sphAct x p).rep⁻¹ * (x * g) ∈ specialSub A (p.spx : Set V) := h
    have h2 : p.rep⁻¹ * g =
        ((x * p.rep)⁻¹ * (sphAct x p).rep) * ((sphAct x p).rep⁻¹ * (x * g)) := by group
    rw [InChamber, h2]
    exact Subgroup.mul_mem _ hq' h1
  · intro h
    have h1 : (sphAct x p).rep⁻¹ * (x * g) =
        ((sphAct x p).rep⁻¹ * (x * p.rep)) * (p.rep⁻¹ * g) := by group
    show (sphAct x p).rep⁻¹ * (x * g) ∈ specialSub A ((sphAct x p).spx : Set V)
    rw [sphAct_spx, h1]
    exact Subgroup.mul_mem _ hq h

omit [Fintype V] in
theorem sphAct_monotone (x : CayGroup A) : Monotone (sphAct (A := A) x) := by
  intro p q hpq
  rw [le_iff_forall_inChamber] at hpq ⊢
  refine ⟨hpq.1, fun g hg => ?_⟩
  have h1 : InChamber (x * (x⁻¹ * g)) (sphAct x p) := by
    rw [mul_inv_cancel_left]
    exact hg
  have h2 : InChamber (x⁻¹ * g) p := (inChamber_sphAct x (x⁻¹ * g) p).1 h1
  have h3 : InChamber (x * (x⁻¹ * g)) (sphAct x q) :=
    (inChamber_sphAct x (x⁻¹ * g) q).2 (hpq.2 _ h2)
  rwa [mul_inv_cancel_left] at h3

omit [Fintype V] in
@[simp] theorem sphAct_one (p : Sph A) : sphAct (1 : CayGroup A) p = p := by
  have h : InChamber p.rep (sphAct (1 : CayGroup A) p) := by
    have := inChamber_sphAct_self (1 : CayGroup A) p
    rwa [one_mul] at this
  have := eq_chamberPt h
  rw [this]
  exact (eq_chamberPt (inChamber_rep p)).symm

omit [Fintype V] in
theorem sphAct_mul (x y : CayGroup A) (p : Sph A) :
    sphAct (x * y) p = sphAct x (sphAct y p) := by
  have h1 : InChamber (x * (y * p.rep)) (sphAct x (sphAct y p)) :=
    (inChamber_sphAct x (y * p.rep) (sphAct y p)).2 (inChamber_sphAct_self y p)
  have h2 : InChamber ((x * y) * p.rep) (sphAct (x * y) p) := inChamber_sphAct_self (x * y) p
  rw [eq_chamberPt h2, eq_chamberPt h1]
  rfl

omit [Fintype V] in
/-- The action of `W` by order automorphisms of the poset of spherical cosets: the deck
transformations of the covering `D → Γ \ D`. -/
theorem sphAct_le_iff (x : CayGroup A) {p q : Sph A} :
    sphAct x p ≤ sphAct x q ↔ p ≤ q := by
  constructor
  · intro h
    have := sphAct_monotone (A := A) x⁻¹ h
    rwa [← sphAct_mul, ← sphAct_mul, inv_mul_cancel, sphAct_one, sphAct_one] at this
  · intro h
    exact sphAct_monotone x h

/-- The action of `W` by order automorphisms of the poset of spherical cosets. -/
noncomputable def sphActIso (x : CayGroup A) : Sph A ≃o Sph A where
  toFun := sphAct x
  invFun := sphAct x⁻¹
  left_inv p := by rw [← sphAct_mul, inv_mul_cancel, sphAct_one]
  right_inv p := by rw [← sphAct_mul, mul_inv_cancel, sphAct_one]
  map_rel_iff' {p q} := sphAct_le_iff x

/-! ### The action is free on the chambers -/

omit [Fintype V] in
/-- **The action is free on the chambers.**  The apex `{g}` is fixed by `x` only for `x = 1`, so
the deck action of `Γ` on the chambers of `D` is free. -/
theorem sphAct_apex_eq_self_iff (x g : CayGroup A) :
    sphAct x (chamberPt g (isSimplex_empty (A := A))) =
      chamberPt g (isSimplex_empty (A := A)) ↔ x = 1 := by
  constructor
  · intro h
    have h1 := congrArg Sph.rep h
    rw [sphAct, chamberPt_empty_rep, chamberPt_empty_rep] at h1
    have h2 : x * g = 1 * g := by rw [one_mul]; exact h1
    exact mul_right_cancel h2
  · rintro rfl
    exact sphAct_one _

omit [Fintype V] in
/-- The action carries the chamber `F_g` to the chamber `F_{x g}`. -/
theorem sphAct_apex (x g : CayGroup A) :
    sphAct x (chamberPt g (isSimplex_empty (A := A))) =
      chamberPt (x * g) (isSimplex_empty (A := A)) := by
  rw [sphAct, chamberPt_empty_rep]

omit [Fintype V] in
/-- The action carries chambers to chambers: `x · F_g = F_{x g}`. -/
theorem inChamber_sphAct_iff (x g : CayGroup A) (p : Sph A) :
    InChamber (x * g) (sphAct x p) ↔ InChamber g p := inChamber_sphAct x g p

end Davis
end FiniteChains
