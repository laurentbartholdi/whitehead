module

public import RequestProject.CoverChainComplex
public import RequestProject.SchreierTransversal

@[expose] public section

/-!
# The Magnus/Blanchfield theorem: the kernel of the Fox vector map is `[Ñ, Ñ]`

Let `F` be the free group on `α`, let `Ñ ◁ F` be a normal subgroup and let `Q = F/Ñ`.
The Fox vector map

`Ñ → ℤ[Q]^α`,  `w ↦ (π(∂w/∂x))_x`

is a homomorphism (`FiniteChains.foxVec_mul`) and kills commutators.  The classical
theorem of Magnus (equivalently, Blanchfield's exactness of the Crowell sequence at
`Ñ/[Ñ, Ñ]`) says that its kernel is *exactly* `[Ñ, Ñ]`.  This file proves that theorem.

The proof is the elementary one, via the Schreier transversal `T` of
`RequestProject/SchreierTransversal.lean`:

* the Fox derivative of a transversal element `t` only involves basis elements `π(s)·e_x`
  with `s ∈ T` and `s·x ∈ T` (`FiniteChains.coefAt_foxVec_rep`);
* consequently the Fox vector of the Schreier generator `s(t, x) = t·x·rep(tx)⁻¹` has
  coefficient `1` at `π(t)·e_x` and coefficient `0` at `π(t')·e_{x'}` for every other
  Schreier pair (`FiniteChains.coefAt_foxVec_schreierGen`);
* the Schreier generators generate `Ñ`, so this triangularity forces the Fox vector map to
  be injective on `Ñ/[Ñ, Ñ]` (`FiniteChains.foxVec_eq_zero_iff`).
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra FreeGroup

variable {α : Type*} [DecidableEq α] (Nsub : Subgroup (FreeGroup α)) [Nsub.Normal]

/-! ### Elementary computations with Fox vectors -/

omit [DecidableEq α] in
theorem qgrp_mul (u v : FreeGroup α) :
    qgrp Nsub (u * v) = qgrp Nsub u * qgrp Nsub v := by
  rw [qgrp, qgrp, qgrp, MonoidAlgebra.single_mul_single, QuotientGroup.mk_mul, mul_one]

/-- The coefficient of the coset of `s` in an element of `ℤ[Q]`. -/
def coefAt (s : FreeGroup α) (z : CoverRing Nsub) : ℤ :=
  z.coeff (QuotientGroup.mk s : FreeGroup α ⧸ Nsub)

omit [DecidableEq α] in
@[simp] theorem coefAt_zero (s : FreeGroup α) : coefAt Nsub s 0 = 0 := rfl

omit [DecidableEq α] in
theorem coefAt_add (s : FreeGroup α) (z w : CoverRing Nsub) :
    coefAt Nsub s (z + w) = coefAt Nsub s z + coefAt Nsub s w := rfl

omit [DecidableEq α] in
omit [Nsub.Normal] in
theorem coefAt_neg (s : FreeGroup α) (z : CoverRing Nsub) :
    coefAt Nsub s (-z) = -coefAt Nsub s z := rfl

omit [DecidableEq α] in
theorem coefAt_sub (s : FreeGroup α) (z w : CoverRing Nsub) :
    coefAt Nsub s (z - w) = coefAt Nsub s z - coefAt Nsub s w := rfl

omit [DecidableEq α] in
omit [Nsub.Normal] in
theorem coefAt_qgrp_self (u : FreeGroup α) : coefAt Nsub u (qgrp Nsub u) = 1 :=
  Finsupp.single_eq_same

omit [DecidableEq α] in
omit [Nsub.Normal] in
theorem coefAt_qgrp_of_ne {s u : FreeGroup α}
    (h : (QuotientGroup.mk u : FreeGroup α ⧸ Nsub) ≠ QuotientGroup.mk s) :
    coefAt Nsub s (qgrp Nsub u) = 0 :=
  Finsupp.single_eq_of_ne (Ne.symm h)

/-- The product rule for Fox vectors, valid for arbitrary words. -/
theorem foxVec_mul' (u v : FreeGroup α) (x : α) :
    foxVec Nsub (u * v) x = foxVec Nsub u x + qgrp Nsub u * foxVec Nsub v x := by
  show proj Nsub (fox x (u * v)) = proj Nsub (fox x u) + qgrp Nsub u * proj Nsub (fox x v)
  rw [fox_mul, map_add, _root_.map_mul (proj Nsub), proj_grp]

/-- The rule for inverses, valid for arbitrary words. -/
theorem foxVec_inv' (u : FreeGroup α) (x : α) :
    foxVec Nsub u⁻¹ x = -(qgrp Nsub u⁻¹ * foxVec Nsub u x) := by
  show proj Nsub (fox x u⁻¹) = -(qgrp Nsub u⁻¹ * proj Nsub (fox x u))
  rw [fox_inv, map_neg, _root_.map_mul (proj Nsub), proj_grp]

@[simp] theorem foxVec_of (x y : α) :
    foxVec Nsub (FreeGroup.of y) x = if x = y then 1 else 0 := by
  show proj Nsub (fox x (FreeGroup.of y)) = _
  rw [fox_of]
  split <;> simp

/-! ### Triangularity of the Fox vectors of the Schreier generators -/

/-- **Claim A.**  The Fox derivative of a transversal element only involves basis elements
`π(s)·e_x` coming from pairs with `s ∈ T` *and* `s·x ∈ T`. -/
theorem coefAt_foxVec_rep (q : FreeGroup α ⧸ Nsub) {s : FreeGroup α} (hs : s ∈ repSet Nsub)
    (x : α) (hsx : s * FreeGroup.of x ∉ repSet Nsub) :
    coefAt Nsub s (foxVec Nsub (rep Nsub q) x) = 0 := by
  have key : ∀ n : ℕ, ∀ q : FreeGroup α ⧸ Nsub, clen Nsub q ≤ n →
      coefAt Nsub s (foxVec Nsub (rep Nsub q) x) = 0 := by
    intro n
    induction n with
    | zero =>
        intro q hq
        rw [rep_of_clen_eq_zero Nsub (Nat.le_zero.1 hq), foxVec_one]
        rfl
    | succ n ih =>
        intro q hq
        by_cases h : clen Nsub q = 0
        · rw [rep_of_clen_eq_zero Nsub h, foxVec_one]
          rfl
        · have hlt := parentData_clen Nsub h
          have hIH : coefAt Nsub s (foxVec Nsub (rep Nsub (parentData Nsub h).1) x) = 0 :=
            ih _ (by omega)
          set t' := rep Nsub (parentData Nsub h).1 with ht'
          have ht'mem : t' ∈ repSet Nsub := rep_mem_repSet Nsub _
          have hstep := rep_mul_letter Nsub h
          rw [← ht'] at hstep
          rcases hy : (parentData Nsub h).2 with ⟨y, b⟩
          rw [hy] at hstep
          cases b with
          | true =>
              have hqrep : rep Nsub q = t' * FreeGroup.of y := hstep
              rw [hqrep, foxVec_mul' Nsub, coefAt_add, hIH, zero_add]
              by_cases hxy : x = y
              · subst hxy
                rw [foxVec_of, if_pos rfl, mul_one]
                by_cases hst : (QuotientGroup.mk t' : FreeGroup α ⧸ Nsub) = QuotientGroup.mk s
                · exfalso
                  have hts : s = t' := eq_of_mk_eq Nsub hs ht'mem hst.symm
                  rw [hts] at hsx
                  exact hsx (by rw [← hqrep]; exact rep_mem_repSet Nsub q)
                · exact coefAt_qgrp_of_ne Nsub hst
              · rw [foxVec_of, if_neg hxy, mul_zero]
                exact coefAt_zero Nsub s
          | false =>
              have hqrep : rep Nsub q = t' * (FreeGroup.of y)⁻¹ := hstep
              rw [hqrep, foxVec_mul' Nsub, coefAt_add, hIH, zero_add]
              by_cases hxy : x = y
              · subst hxy
                rw [foxVec_inv' Nsub, foxVec_of, if_pos rfl, mul_one, mul_neg, ← qgrp_mul,
                  coefAt_neg]
                by_cases hst : (QuotientGroup.mk (t' * (FreeGroup.of x)⁻¹) :
                    FreeGroup α ⧸ Nsub) = QuotientGroup.mk s
                · exfalso
                  have hmem : t' * (FreeGroup.of x)⁻¹ ∈ repSet Nsub := by
                    rw [← hqrep]; exact rep_mem_repSet Nsub q
                  have hts : s = t' * (FreeGroup.of x)⁻¹ := eq_of_mk_eq Nsub hs hmem hst.symm
                  rw [hts] at hsx
                  refine hsx ?_
                  rw [inv_mul_cancel_right]
                  exact ht'mem
                · rw [coefAt_qgrp_of_ne Nsub hst, neg_zero]
              · rw [foxVec_inv' Nsub, foxVec_of, if_neg hxy, mul_zero, neg_zero, mul_zero]
                exact coefAt_zero Nsub s
  exact key (clen Nsub q) q le_rfl

/-- **Claim B.**  Triangularity of the Fox vectors of the Schreier generators: at the
"leading" coefficient of its own Schreier pair a generator has coefficient `1`, and at the
leading coefficient of any other Schreier pair it has coefficient `0`. -/
theorem coefAt_foxVec_schreierGen {t : FreeGroup α} (ht : t ∈ repSet Nsub) (y : α)
    {s : FreeGroup α} (hs : s ∈ repSet Nsub) (x : α) (hsx : s * FreeGroup.of x ∉ repSet Nsub) :
    coefAt Nsub s (foxVec Nsub (schreierGen Nsub t y) x)
      = if s = t ∧ x = y then 1 else 0 := by
  obtain ⟨qt, rfl⟩ := ht
  set t := rep Nsub qt with ht
  set u := rep Nsub (QuotientGroup.mk (t * FreeGroup.of y)) with hu
  have hprod : schreierGen Nsub t y = t * FreeGroup.of y * u⁻¹ := rfl
  have hone : qgrp Nsub (t * FreeGroup.of y * u⁻¹) = 1 :=
    qgrp_eq_one_of_mem Nsub (schreierGen_mem Nsub t y)
  have hexp : foxVec Nsub (schreierGen Nsub t y) x
      = foxVec Nsub t x + qgrp Nsub t * foxVec Nsub (FreeGroup.of y) x
        - foxVec Nsub u x := by
    rw [hprod, foxVec_mul' Nsub, foxVec_mul' Nsub, foxVec_inv' Nsub]
    rw [mul_neg, ← mul_assoc, ← qgrp_mul, hone, one_mul, ← sub_eq_add_neg]
  rw [hexp, coefAt_sub, coefAt_add]
  rw [coefAt_foxVec_rep Nsub qt hs x hsx, coefAt_foxVec_rep Nsub _ hs x hsx, zero_add, sub_zero]
  by_cases hxy : x = y
  · subst hxy
    rw [foxVec_of, if_pos rfl, mul_one]
    by_cases hst : s = t
    · subst hst
      rw [coefAt_qgrp_self, if_pos ⟨rfl, rfl⟩]
    · have hne : (QuotientGroup.mk t : FreeGroup α ⧸ Nsub) ≠ QuotientGroup.mk s := fun hq =>
        hst (eq_of_mk_eq Nsub hs ⟨qt, rfl⟩ hq.symm)
      rw [coefAt_qgrp_of_ne Nsub hne, if_neg (by tauto)]
  · rw [foxVec_of, if_neg hxy, mul_zero, if_neg (by tauto)]
    exact coefAt_zero Nsub s

/-! ### The Schreier generators of the proper pairs -/

omit [DecidableEq α] in
/-- A Schreier generator attached to a pair with `t·x ∈ T` is trivial. -/
theorem schreierGen_eq_one {t : FreeGroup α} (x : α)
    (h : t * FreeGroup.of x ∈ repSet Nsub) : schreierGen Nsub t x = 1 := by
  rw [schreierGen, rep_mk_of_mem Nsub h, mul_inv_cancel]

/-- The Schreier generators attached to the pairs `(t, x)` with `t ∈ T` and `t·x ∉ T`; the
remaining Schreier generators are trivial. -/
def properSchreierSet : Set (FreeGroup α) :=
  {g | ∃ (q : FreeGroup α ⧸ Nsub) (x : α),
    rep Nsub q * FreeGroup.of x ∉ repSet Nsub ∧ g = schreierGen Nsub (rep Nsub q) x}

omit [DecidableEq α] in
theorem properSchreierSet_subset : properSchreierSet Nsub ⊆ (Nsub : Set (FreeGroup α)) := by
  rintro g ⟨q, x, -, rfl⟩
  exact schreierGen_mem Nsub _ _

omit [DecidableEq α] in
theorem closure_properSchreierSet : Subgroup.closure (properSchreierSet Nsub) = Nsub := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    exact properSchreierSet_subset Nsub
  · have hle : Subgroup.closure (schreierSet Nsub) ≤ Subgroup.closure (properSchreierSet Nsub) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨⟨q, x⟩, rfl⟩
      by_cases h : rep Nsub q * FreeGroup.of x ∈ repSet Nsub
      · show schreierGen Nsub (rep Nsub q) x ∈ _
        rw [schreierGen_eq_one Nsub x h]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure ⟨q, x, h, rfl⟩
    intro w hw
    refine hle ?_
    rw [closure_schreierGen Nsub]
    exact hw

/-! ### A triangularity criterion in an abelian group -/

/-- If an abelian group is generated by a family `g` and carries functionals `c` with
`c i (g j) = δ_{ij}`, then an element killed by all the functionals is zero. -/
theorem eq_zero_of_forall_coefHom {M : Type*} [AddCommGroup M] {Idx : Type*} (g : Idx → M)
    (hgen : ∀ a : M, a ∈ AddSubgroup.closure (Set.range g))
    (c : Idx → (M →+ ℤ)) (hdiag : ∀ i, c i (g i) = 1)
    (hoff : ∀ i j, j ≠ i → c i (g j) = 0)
    {a : M} (ha : ∀ i, c i a = 0) : a = 0 := by
  classical
  have key : ∀ b ∈ AddSubgroup.closure (Set.range g),
      ∃ d : Idx →₀ ℤ, b = d.sum fun i n => n • g i := by
    intro b hb
    induction hb using AddSubgroup.closure_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact ⟨Finsupp.single i 1, by simp⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ ihx ihy =>
        obtain ⟨d₁, h₁⟩ := ihx
        obtain ⟨d₂, h₂⟩ := ihy
        refine ⟨d₁ + d₂, ?_⟩
        rw [h₁, h₂, Finsupp.sum_add_index' (by simp) (fun i n m => by rw [add_smul])]
    | neg x _ ih =>
        obtain ⟨d, hd⟩ := ih
        refine ⟨-d, ?_⟩
        rw [hd, Finsupp.sum_neg_index (by simp)]
        simp [neg_smul, Finsupp.sum_neg]
  obtain ⟨d, rfl⟩ := key a (hgen a)
  have hd : ∀ i, d i = 0 := by
    intro i
    have h0 := ha i
    rw [map_finsuppSum] at h0
    have hterm : ∀ j : Idx, ∀ n : ℤ, c i (n • g j) = if j = i then n else 0 := by
      intro j n
      rw [map_zsmul]
      by_cases hji : j = i
      · subst hji
        rw [hdiag j, if_pos rfl, smul_eq_mul, mul_one]
      · rw [hoff i j hji, if_neg hji, smul_zero]
    rw [Finsupp.sum_congr (g2 := fun j n => if j = i then n else 0)
      (fun j _ => hterm j (d j))] at h0
    rw [Finsupp.sum_ite_eq' d i (fun _ n => n)] at h0
    by_cases hi : i ∈ d.support
    · rwa [if_pos hi] at h0
    · exact Finsupp.notMem_support_iff.1 hi
  have hzero : d = 0 := Finsupp.ext hd
  rw [hzero]
  simp

/-! ### The Fox vector map on `Ñ` and its kernel -/

/-- The Fox vector map, as a homomorphism on `Ñ`. -/
noncomputable def foxHomNsub : Nsub →* Multiplicative (α → CoverRing Nsub) where
  toFun w := Multiplicative.ofAdd (foxVec Nsub (w : FreeGroup α))
  map_one' := by
    show Multiplicative.ofAdd (foxVec Nsub (1 : FreeGroup α)) = 1
    rw [foxVec_one]
    rfl

  map_mul' := fun a b => by
    show Multiplicative.ofAdd (foxVec Nsub ((a : FreeGroup α) * (b : FreeGroup α))) = _
    rw [foxVec_mul a.2]
    rfl

/-- The Fox vector map on the abelianization of `Ñ`. -/
noncomputable def foxAb : Abelianization Nsub →* Multiplicative (α → CoverRing Nsub) :=
  Abelianization.lift (foxHomNsub Nsub)

/-- The Fox vector map on the abelianization of `Ñ`, written additively. -/
noncomputable def foxAbAdd : Additive (Abelianization Nsub) →+ (α → CoverRing Nsub) where
  toFun a := Multiplicative.toAdd (foxAb Nsub (Additive.toMul a))
  map_zero' := by
    show Multiplicative.toAdd (foxAb Nsub 1) = 0
    rw [_root_.map_one]
    rfl
  map_add' := fun a b => by
    show Multiplicative.toAdd (foxAb Nsub (Additive.toMul a * Additive.toMul b)) = _
    rw [_root_.map_mul]
    rfl

theorem foxAbAdd_of (w : Nsub) :
    foxAbAdd Nsub (Additive.ofMul (Abelianization.of w)) = foxVec Nsub (w : FreeGroup α) := by
  show Multiplicative.toAdd (foxAb Nsub (Abelianization.of w)) = _
  rw [foxAb, Abelianization.lift_apply_of]
  rfl

/-- The index set of the Schreier generators: pairs `(q, x)` with `rep q · x ∉ T`. -/
def SchreierIdx : Type _ :=
  {p : (FreeGroup α ⧸ Nsub) × α // rep Nsub p.1 * FreeGroup.of p.2 ∉ repSet Nsub}

/-- The image in the abelianization of `Ñ` of the Schreier generator of a proper pair. -/
noncomputable def schreierClass (i : SchreierIdx Nsub) : Additive (Abelianization Nsub) :=
  Additive.ofMul (Abelianization.of
    ⟨schreierGen Nsub (rep Nsub i.1.1) i.1.2, schreierGen_mem Nsub _ _⟩)

/-- The functional reading off the leading coefficient of a Schreier pair. -/
noncomputable def schreierCoef (i : SchreierIdx Nsub) :
    Additive (Abelianization Nsub) →+ ℤ :=
  (Finsupp.applyAddHom (QuotientGroup.mk (rep Nsub i.1.1) : FreeGroup α ⧸ Nsub)).comp
    ((MonoidAlgebra.coeffAddEquiv).toAddMonoidHom.comp
      ((Pi.evalAddMonoidHom (fun _ : α => CoverRing Nsub) i.1.2).comp (foxAbAdd Nsub)))

theorem schreierCoef_apply (i : SchreierIdx Nsub) (a : Additive (Abelianization Nsub)) :
    schreierCoef Nsub i a = coefAt Nsub (rep Nsub i.1.1) (foxAbAdd Nsub a i.1.2) := rfl

/-- **The triangularity relation** between the Schreier generators and the leading
coefficients. -/
theorem schreierCoef_schreierClass_self (i : SchreierIdx Nsub) :
    schreierCoef Nsub i (schreierClass Nsub i) = 1 := by
  rw [schreierCoef_apply, schreierClass, foxAbAdd_of]
  rw [coefAt_foxVec_schreierGen Nsub (rep_mem_repSet Nsub i.1.1) i.1.2
    (rep_mem_repSet Nsub i.1.1) i.1.2 i.2, if_pos ⟨rfl, rfl⟩]

theorem schreierCoef_schreierClass_of_ne (i j : SchreierIdx Nsub) (hij : j ≠ i) :
    schreierCoef Nsub i (schreierClass Nsub j) = 0 := by
  rw [schreierCoef_apply, schreierClass, foxAbAdd_of]
  rw [coefAt_foxVec_schreierGen Nsub (rep_mem_repSet Nsub j.1.1) j.1.2
    (rep_mem_repSet Nsub i.1.1) i.1.2 i.2]
  rw [if_neg ?_]
  rintro ⟨h1, h2⟩
  refine hij ?_
  have hq : i.1.1 = j.1.1 := by
    have := congrArg (fun t : FreeGroup α => (QuotientGroup.mk t : FreeGroup α ⧸ Nsub)) h1
    simpa [mk_rep] using this
  exact Subtype.ext (Prod.ext hq.symm h2.symm)

omit [DecidableEq α] in
/-- The Schreier classes generate the abelianization of `Ñ`. -/
theorem closure_schreierClass (a : Additive (Abelianization Nsub)) :
    a ∈ AddSubgroup.closure (Set.range (schreierClass Nsub)) := by
  obtain ⟨u, hu⟩ := Quotient.exists_rep (Additive.toMul a)
  have ha : a = Additive.ofMul (Abelianization.of u) := by
    apply Additive.toMul.injective
    exact hu.symm
  subst ha
  have hmem : u ∈ Subgroup.closure ((Nsub.subtype) ⁻¹' properSchreierSet Nsub) := by
    have hmap : Subgroup.map Nsub.subtype
        (Subgroup.closure ((Nsub.subtype) ⁻¹' properSchreierSet Nsub)) = Nsub := by
      have hsub : properSchreierSet Nsub ⊆ Set.range ⇑Nsub.subtype := fun g hg =>
        ⟨⟨g, properSchreierSet_subset Nsub hg⟩, rfl⟩
      rw [MonoidHom.map_closure, Set.image_preimage_eq_inter_range,
        Set.inter_eq_self_of_subset_left hsub]
      exact closure_properSchreierSet Nsub
    have htop : Subgroup.map Nsub.subtype (⊤ : Subgroup Nsub) = Nsub := by
      ext x
      simp [Subgroup.mem_map]
    have := Subgroup.map_injective (f := Nsub.subtype) Subtype.val_injective (hmap.trans htop.symm)
    rw [this]
    trivial
  clear hu
  induction hmem using Subgroup.closure_induction with
  | mem v hv =>
      obtain ⟨q, x, hnot, hval⟩ := hv
      refine AddSubgroup.subset_closure (Set.mem_range.2 ⟨⟨(q, x), hnot⟩, ?_⟩)
      unfold schreierClass
      congr 2
      exact Subtype.ext hval.symm
  | one =>
      have : Additive.ofMul (Abelianization.of (1 : Nsub)) = 0 := by
        show Additive.ofMul (Abelianization.of (1 : Nsub)) = Additive.ofMul 1
        rw [_root_.map_one]
      rw [this]
      exact AddSubgroup.zero_mem _
  | mul v w _ _ ihv ihw =>
      have : Additive.ofMul (Abelianization.of (v * w))
          = Additive.ofMul (Abelianization.of v) + Additive.ofMul (Abelianization.of w) := by
        show Additive.ofMul (Abelianization.of (v * w))
          = Additive.ofMul (Abelianization.of v * Abelianization.of w)
        rw [_root_.map_mul]
      rw [this]
      exact AddSubgroup.add_mem _ ihv ihw
  | inv v _ ihv =>
      have : Additive.ofMul (Abelianization.of v⁻¹)
          = -Additive.ofMul (Abelianization.of v) := by
        show Additive.ofMul (Abelianization.of v⁻¹)
          = Additive.ofMul (Abelianization.of v)⁻¹
        rw [_root_.map_inv]
      rw [this]
      exact AddSubgroup.neg_mem _ ihv

/-- **The Magnus/Blanchfield theorem.**  For `w ∈ Ñ`, the Fox vector of `w` vanishes exactly
when `w` lies in the commutator subgroup `[Ñ, Ñ]`. -/
theorem foxVec_eq_zero_iff {w : FreeGroup α} (hw : w ∈ Nsub) :
    foxVec Nsub w = 0 ↔ w ∈ ⁅Nsub, Nsub⁆ := by
  constructor
  · intro h0
    have hzero : Additive.ofMul (Abelianization.of (⟨w, hw⟩ : Nsub)) = 0 := by
      refine eq_zero_of_forall_coefHom (schreierClass Nsub) (closure_schreierClass Nsub)
        (schreierCoef Nsub) (schreierCoef_schreierClass_self Nsub)
        (schreierCoef_schreierClass_of_ne Nsub) ?_
      intro i
      rw [schreierCoef_apply, foxAbAdd_of]
      show coefAt Nsub (rep Nsub i.1.1) (foxVec Nsub w i.1.2) = 0
      rw [h0]
      rfl
    have hcomm : (⟨w, hw⟩ : Nsub) ∈ commutator Nsub := by
      have h1 : Abelianization.of (⟨w, hw⟩ : Nsub) = 1 := by
        apply Additive.ofMul.injective
        exact hzero
      rw [Abelianization.of] at h1
      exact (QuotientGroup.eq_one_iff _).1 h1
    rw [← Subgroup.map_subtype_commutator Nsub]
    exact ⟨⟨w, hw⟩, hcomm, rfl⟩
  · intro hcomm
    have hker : ⁅Nsub, Nsub⁆ ≤ (foxHomNsub Nsub).ker.map Nsub.subtype := by
      rw [← Subgroup.map_subtype_commutator Nsub]
      exact Subgroup.map_mono (Abelianization.commutator_subset_ker (foxHomNsub Nsub))
    obtain ⟨u, hu, huw⟩ := hker hcomm
    have hu' : (foxHomNsub Nsub) u = 1 := hu
    have hzero : foxVec Nsub (u : FreeGroup α) = 0 := hu'
    rw [← huw]
    exact hzero

end FiniteChains
