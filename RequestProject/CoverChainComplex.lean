module

public import RequestProject.MonoidAlgebraMapDomain
public import RequestProject.FoxLinear

@[expose] public section

/-!
# The chain complex of the cover `K_N` and the Crowell exact sequence

Let `K` be the two-complex of a finite presentation `⟨x_1, …, x_n | r_1, …, r_m⟩`, let `F`
be the free group on the generators and let `Ñ ◁ F` be the normal subgroup corresponding
(Remark 1 of the paper) to a normal subgroup `N` of `G = π₁(K)`; write `Q = F/Ñ` for the
deck group of the cover `K_N`.  The cellular chain complex of `K_N` is the complex of free
left `ℤ[Q]`-modules

`ℤ[Q]^m --∂₂--> ℤ[Q]^n --∂₁--> ℤ[Q]`,
`∂₂(e_j) = (π(∂r_j/∂x_i))_i`,  `∂₁(e_i) = x_i - 1`,

where `π : ℤ[F] → ℤ[Q]` is the projection and `∂r/∂x` are the Fox derivatives.

This file builds that complex and proves everything about it that the paper uses:

* `FiniteChains.bdry1_bdry2` : it is a complex, `∂₁ ∘ ∂₂ = 0`;
* `FiniteChains.exists_bdry1_preimage` : the image of `∂₁` is the augmentation ideal, i.e.
  `H̃₀(K_N) = 0` — the cover is connected;
* `FiniteChains.exists_mem_of_bdry1_eq_zero` : **the Crowell exact sequence**, `ker ∂₁`
  consists exactly of the Fox vectors `(π(∂w/∂x_i))_i` of the elements `w ∈ Ñ`;
* `FiniteChains.exists_bdry2_preimage` : if `N` is perfect, i.e.
  `Ñ ≤ ⟪r_1, …, r_m⟫ ⊔ [Ñ, Ñ]`, then `ker ∂₁ = im ∂₂`, i.e. `H₁(K_N) = 0`;
* `FiniteChains.cover_acyclic` : consequently, if moreover `∂₂` is injective (that is
  `H₂(K_N) = ker ∂₂ = 0`, the requirements (2.2) of Section 2), the chain complex of the
  cover is acyclic.

This is the algebraic content of the passage "`N` perfect and `ker ∂_{2,N} = 0` implies
`K_N` acyclic" used in the proof of `(1) ⇒ (2)` of Theorem A.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped commutatorElement

namespace FiniteChains

open MonoidAlgebra

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (Nsub : Subgroup (FreeGroup α)) [Nsub.Normal]

/-- The group ring `ℤ[Q]` of the deck group `Q = F/Ñ` of the cover. -/
abbrev CoverRing : Type _ := MonoidAlgebra ℤ (FreeGroup α ⧸ Nsub)

/-- The projection `π : ℤ[F] → ℤ[Q]`. -/
noncomputable def proj : FreeGroupRing α →+* CoverRing Nsub :=
  MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' Nsub)

/-- The image of a word in `ℤ[Q]`. -/
noncomputable def qgrp (g : FreeGroup α) : CoverRing Nsub :=
  MonoidAlgebra.single (QuotientGroup.mk g) 1

/-- The augmentation `ℤ[Q] → ℤ`. -/
noncomputable def augQ : CoverRing Nsub →+* ℤ :=
  (MonoidAlgebra.lift ℤ ℤ (FreeGroup α ⧸ Nsub) 1).toRingHom

/-- A set-theoretic lift `ℤ[Q] → ℤ[F]` of the projection. -/
noncomputable def liftQ (z : CoverRing Nsub) : FreeGroupRing α :=
  MonoidAlgebra.mapDomain (fun q => Quotient.out q) z

omit [Fintype α] [DecidableEq α] in
theorem proj_apply (b : FreeGroupRing α) :
    proj Nsub b = MonoidAlgebra.mapDomain (fun g => (QuotientGroup.mk g : FreeGroup α ⧸ Nsub)) b := rfl

omit [Fintype α] [DecidableEq α] in
@[simp] theorem proj_single (g : FreeGroup α) (n : ℤ) :
    proj Nsub (single g n) = single (QuotientGroup.mk g : FreeGroup α ⧸ Nsub) n := by
  rw [proj_apply]
  exact MonoidAlgebra.mapDomain_single

omit [Fintype α] [DecidableEq α] in
theorem proj_grp (g : FreeGroup α) : proj Nsub (grp g) = qgrp Nsub g := by
  rw [grp_eq_single, proj_single, qgrp]

omit [Fintype α] [DecidableEq α] in
theorem qgrp_eq_one_of_mem {g : FreeGroup α} (hg : g ∈ Nsub) : qgrp Nsub g = 1 := by
  have h : (QuotientGroup.mk g : FreeGroup α ⧸ Nsub) = 1 := (QuotientGroup.eq_one_iff g).2 hg
  rw [qgrp, h]
  rfl

omit [Fintype α] [DecidableEq α] in
theorem proj_grp_of_mem {g : FreeGroup α} (hg : g ∈ Nsub) : proj Nsub (grp g) = 1 := by
  rw [proj_grp, qgrp_eq_one_of_mem Nsub hg]

omit [Fintype α] [DecidableEq α] in
@[simp] theorem augQ_single (q : FreeGroup α ⧸ Nsub) (n : ℤ) : augQ Nsub (single q n) = n := by
  simp [augQ]

omit [Fintype α] [DecidableEq α] in
theorem augQ_proj (b : FreeGroupRing α) : augQ Nsub (proj Nsub b) = aug b := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b₁ b₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add]
  | single g n => rw [proj_single, augQ_single, aug_single]

omit [Fintype α] [DecidableEq α] in
theorem proj_liftQ (z : CoverRing Nsub) : proj Nsub (liftQ Nsub z) = z := by
  have hcomp : (fun q : FreeGroup α ⧸ Nsub => (QuotientGroup.mk (Quotient.out q) : FreeGroup α ⧸ Nsub))
      = id := funext fun q => QuotientGroup.out_eq' q
  rw [proj_apply, liftQ, ← MonoidAlgebra.mapDomain_comp]
  show MonoidAlgebra.mapDomain (fun q : FreeGroup α ⧸ Nsub =>
    (QuotientGroup.mk (Quotient.out q) : FreeGroup α ⧸ Nsub)) z = z
  rw [hcomp, MonoidAlgebra.mapDomain_id]

/-! ### The Fox vector of a word -/

/-- The Fox vector `(π(∂w/∂x_i))_i ∈ ℤ[Q]^n` of a word. -/
noncomputable def foxVec (w : FreeGroup α) : α → CoverRing Nsub :=
  fun i => proj Nsub (fox i w)

omit [Fintype α] in
@[simp] theorem foxVec_one : foxVec Nsub 1 = 0 := by
  funext i; simp [foxVec]

variable {Nsub}

omit [Fintype α] in
theorem foxVec_mul {v : FreeGroup α} (hv : v ∈ Nsub) (w : FreeGroup α) :
    foxVec Nsub (v * w) = foxVec Nsub v + foxVec Nsub w := by
  funext i
  simp only [foxVec, fox_mul, map_add, map_mul, proj_grp_of_mem Nsub hv, one_mul, Pi.add_apply]

omit [Fintype α] in
theorem foxVec_inv {v : FreeGroup α} (hv : v ∈ Nsub) :
    foxVec Nsub v⁻¹ = - foxVec Nsub v := by
  have h := foxVec_mul (Subgroup.inv_mem _ hv) v
  rw [inv_mul_cancel, foxVec_one] at h
  have h' : foxVec Nsub v⁻¹ + foxVec Nsub v = 0 := h.symm
  exact eq_neg_of_add_eq_zero_left h'

omit [Fintype α] in
theorem foxVec_conj {r : FreeGroup α} (hr : r ∈ Nsub) (f : FreeGroup α) :
    foxVec Nsub (f * r * f⁻¹) = proj Nsub (grp f) • foxVec Nsub r := by
  funext i
  have hfox : fox i (f * r * f⁻¹)
      = fox i f + grp f * fox i r + grp (f * r) * fox i f⁻¹ := by
    rw [fox_mul, fox_mul]
  have hff : proj Nsub (grp f) * proj Nsub (grp f⁻¹) = 1 := by
    rw [← map_mul, ← grp_mul, mul_inv_cancel, grp_one, map_one]
  simp only [foxVec, Pi.smul_apply, smul_eq_mul, hfox, fox_inv i f, grp_mul, map_add, map_mul,
    map_neg, proj_grp_of_mem Nsub hr, mul_one]
  rw [mul_neg, ← mul_assoc, hff, one_mul]
  abel

omit [Fintype α] in
theorem foxVec_zpow {r : FreeGroup α} (hr : r ∈ Nsub) (n : ℤ) :
    foxVec Nsub (r ^ n) = n • foxVec Nsub r := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
      have hmem : r ^ (k : ℤ) ∈ Nsub := Subgroup.zpow_mem _ hr _
      rw [zpow_add_one, foxVec_mul hmem, ih, add_smul, one_smul]
  | pred k ih =>
      have hmem : r ^ (-(k : ℤ)) ∈ Nsub := Subgroup.zpow_mem _ hr _
      rw [zpow_sub_one, foxVec_mul hmem, foxVec_inv hr, ih, sub_smul, one_smul, sub_eq_add_neg]

/-! ### The module of Fox vectors -/

/-- The set of Fox vectors of the elements of `Ñ`; by the Crowell exact sequence this is
exactly the module of `1`-cycles of the cover. -/
noncomputable def foxMod : Submodule (CoverRing Nsub) (α → CoverRing Nsub) where
  carrier := {c | ∃ r ∈ Nsub, c = foxVec Nsub r}
  zero_mem' := ⟨1, Subgroup.one_mem _, by simp⟩
  add_mem' := by
    rintro a b ⟨r, hr, rfl⟩ ⟨s, hs, rfl⟩
    exact ⟨r * s, Subgroup.mul_mem _ hr hs, by rw [foxVec_mul hr]⟩
  smul_mem' := by
    rintro u a ⟨r, hr, rfl⟩
    induction u using MonoidAlgebra.induction_linear with
    | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
    | add u₁ u₂ h₁ h₂ =>
        obtain ⟨r₁, hr₁, e₁⟩ := h₁
        obtain ⟨r₂, hr₂, e₂⟩ := h₂
        refine ⟨r₁ * r₂, Subgroup.mul_mem _ hr₁ hr₂, ?_⟩
        rw [foxVec_mul hr₁, ← e₁, ← e₂, add_smul]
    | single q n =>
        obtain ⟨f, rfl⟩ := Quotient.exists_rep q
        have hconj : f * r * f⁻¹ ∈ Nsub := Subgroup.Normal.conj_mem ‹Nsub.Normal› r hr f
        refine ⟨(f * r * f⁻¹) ^ n, Subgroup.zpow_mem _ hconj n, ?_⟩
        have hsingle : (single (QuotientGroup.mk f : FreeGroup α ⧸ Nsub) n : CoverRing Nsub)
            = n • proj Nsub (grp f) := by
          rw [proj_grp, qgrp, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
        rw [foxVec_zpow hconj, foxVec_conj hr, hsingle, smul_assoc]

/-! ### The kernel of the projection `ℤ[F] → ℤ[Q]` -/

/-- Reindexing of a group-ring element along a map of the free group, viewed on `ℤ[F]`. -/
noncomputable def mapDom (φ : FreeGroup α → FreeGroup α) (c : FreeGroupRing α) :
    FreeGroupRing α := MonoidAlgebra.mapDomain φ c

omit [Fintype α] [DecidableEq α] in
theorem mapDom_add (φ : FreeGroup α → FreeGroup α) (c d : FreeGroupRing α) :
    mapDom φ (c + d) = mapDom φ c + mapDom φ d := MonoidAlgebra.mapDomain_add φ c d

omit [Fintype α] [DecidableEq α] in
theorem mapDom_single (φ : FreeGroup α → FreeGroup α) (g : FreeGroup α) (n : ℤ) :
    mapDom φ (single g n) = single (φ g) n := MonoidAlgebra.mapDomain_single


variable (Nsub)

/-- The left ideal of `ℤ[F]` generated by the elements `r - 1` with `r ∈ Ñ`. -/
noncomputable def relIdeal : Submodule (FreeGroupRing α) (FreeGroupRing α) :=
  Submodule.span (FreeGroupRing α) {y | ∃ r ∈ Nsub, y = grp r - 1}

omit [Fintype α] [DecidableEq α] in
theorem mem_relIdeal_of_proj_eq_zero (b : FreeGroupRing α) (hb : proj Nsub b = 0) :
    b ∈ relIdeal Nsub := by
  classical
  set φ : FreeGroup α → FreeGroup α :=
    fun g => Quotient.out (QuotientGroup.mk g : FreeGroup α ⧸ Nsub) with hφ
  have hmap : mapDom φ b = 0 := by
    show MonoidAlgebra.mapDomain φ b = 0
    have hcomp : MonoidAlgebra.mapDomain φ b
        = MonoidAlgebra.mapDomain (fun q : FreeGroup α ⧸ Nsub => Quotient.out q)
            (MonoidAlgebra.mapDomain (fun g => (QuotientGroup.mk g : FreeGroup α ⧸ Nsub)) b) :=
      MonoidAlgebra.mapDomain_comp _ _ b
    rw [hcomp, ← proj_apply, hb, MonoidAlgebra.mapDomain_zero]
  have key : ∀ c : FreeGroupRing α, c - mapDom φ c ∈ relIdeal Nsub := by
    intro c
    induction c using MonoidAlgebra.induction_linear with
    | zero =>
        have hz : (0 : FreeGroupRing α) - mapDom φ 0 = 0 := by
          rw [show mapDom φ (0 : FreeGroupRing α) = 0 from MonoidAlgebra.mapDomain_zero φ, sub_zero]
        rw [hz]
        exact Submodule.zero_mem _
    | add c₁ c₂ h₁ h₂ =>
        have hsplit : (c₁ + c₂) - mapDom φ (c₁ + c₂)
            = (c₁ - mapDom φ c₁) + (c₂ - mapDom φ c₂) := by
          rw [mapDom_add]; abel
        rw [hsplit]
        exact Submodule.add_mem _ h₁ h₂
    | single g n =>
        have hmk : (QuotientGroup.mk (φ g) : FreeGroup α ⧸ Nsub) = QuotientGroup.mk g :=
          QuotientGroup.out_eq' _
        have hmem : (φ g)⁻¹ * g ∈ Nsub := QuotientGroup.eq.1 hmk
        have hmapd : mapDom φ (single g n : FreeGroupRing α) = single (φ g) n :=
          mapDom_single φ g n
        have hgrp : grp (φ g) * (grp ((φ g)⁻¹ * g) - 1) = grp g - grp (φ g) := by
          rw [mul_sub, ← grp_mul, mul_inv_cancel_left, mul_one]
        have hrewrite : (single g n : FreeGroupRing α) - mapDom φ (single g n : FreeGroupRing α)
            = ((n : ℤ) : FreeGroupRing α) * (grp (φ g) * (grp ((φ g)⁻¹ * g) - 1)) := by
          rw [hmapd, hgrp, single_eq_smul_grp, single_eq_smul_grp, ← smul_sub, zsmul_eq_mul]
        rw [hrewrite]
        have hgen : grp ((φ g)⁻¹ * g) - 1 ∈ relIdeal Nsub :=
          Submodule.subset_span ⟨_, hmem, rfl⟩
        have h1 : grp (φ g) * (grp ((φ g)⁻¹ * g) - 1) ∈ relIdeal Nsub := by
          simpa [smul_eq_mul] using Submodule.smul_mem (relIdeal Nsub) (grp (φ g)) hgen
        simpa [smul_eq_mul] using
          Submodule.smul_mem (relIdeal Nsub) (((n : ℤ) : FreeGroupRing α)) h1
  have hb' := key b
  rwa [hmap, sub_zero] at hb'

/-! ### The Fox vector of a ring element -/

/-- The Fox vector of an element of `ℤ[F]`, i.e. the vector of the linearly extended Fox
derivatives, projected to `ℤ[Q]`. -/
noncomputable def foxProj (b : FreeGroupRing α) : α → CoverRing Nsub :=
  fun i => proj Nsub (foxLin i b)

omit [Fintype α] in
@[simp] theorem foxProj_zero : foxProj Nsub 0 = 0 := by
  funext i; simp [foxProj]

omit [Fintype α] in
theorem foxProj_add (b₁ b₂ : FreeGroupRing α) :
    foxProj Nsub (b₁ + b₂) = foxProj Nsub b₁ + foxProj Nsub b₂ := by
  funext i; simp [foxProj]

omit [Fintype α] in
theorem foxProj_grp (w : FreeGroup α) : foxProj Nsub (grp w) = foxVec Nsub w := by
  funext i; simp [foxProj, foxVec]

omit [Fintype α] in
theorem foxProj_mul_of_aug_zero (u b : FreeGroupRing α) (hb : aug b = 0) :
    foxProj Nsub (u * b) = proj Nsub u • foxProj Nsub b := by
  funext i
  simp only [foxProj, foxLin_mul, hb, zero_smul, zero_add, map_mul, Pi.smul_apply, smul_eq_mul]

omit [Fintype α] in
theorem foxProj_mem_foxMod (b : FreeGroupRing α) (hb : proj Nsub b = 0) :
    foxProj Nsub b ∈ foxMod (Nsub := Nsub) := by
  have hmem := mem_relIdeal_of_proj_eq_zero Nsub b hb
  refine (Submodule.span_induction
    (p := fun y _ => aug y = 0 ∧ foxProj Nsub y ∈ foxMod (Nsub := Nsub)) ?_ ?_ ?_ ?_ hmem).2
  · rintro y ⟨r, hr, rfl⟩
    refine ⟨by simp [map_sub], ?_⟩
    have hval : foxProj Nsub (grp r - 1) = foxVec Nsub r := by
      funext i
      have h1 : foxLin i (1 : FreeGroupRing α) = 0 := by
        rw [← grp_one, foxLin_grp, fox_one]
      simp only [foxProj, foxVec, map_sub, foxLin_grp, h1, sub_zero]
    rw [hval]
    exact ⟨r, hr, rfl⟩
  · exact ⟨by simp, Submodule.zero_mem _⟩
  · rintro x y hx hy ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨by rw [map_add, hx1, hy1, add_zero], by
      rw [foxProj_add]; exact Submodule.add_mem _ hx2 hy2⟩
  · rintro a x hx ⟨hx1, hx2⟩
    refine ⟨by rw [smul_eq_mul, map_mul, hx1, mul_zero], ?_⟩
    rw [smul_eq_mul, foxProj_mul_of_aug_zero Nsub a x hx1]
    exact Submodule.smul_mem _ _ hx2

/-! ### The boundary maps of the cover -/

/-- The boundary `∂₁ : ℤ[Q]^n → ℤ[Q]`, `∂₁(e_i) = x_i - 1`. -/
noncomputable def bdry1 (c : α → CoverRing Nsub) : CoverRing Nsub :=
  ∑ i : α, c i * (qgrp Nsub (FreeGroup.of i) - 1)

omit [DecidableEq α] in
theorem bdry1_add (c d : α → CoverRing Nsub) :
    bdry1 Nsub (c + d) = bdry1 Nsub c + bdry1 Nsub d := by
  simp only [bdry1, Pi.add_apply, add_mul, Finset.sum_add_distrib]

omit [DecidableEq α] in
theorem augQ_bdry1 (c : α → CoverRing Nsub) : augQ Nsub (bdry1 Nsub c) = 0 := by
  simp only [bdry1, map_sum, map_mul, map_sub, map_one, qgrp, augQ_single, sub_self, mul_zero,
    Finset.sum_const_zero]

/-- The Fox vector of an element of `Ñ` is a cycle. -/
theorem bdry1_foxVec {w : FreeGroup α} (hw : w ∈ Nsub) : bdry1 Nsub (foxVec Nsub w) = 0 := by
  have h := fox_fundamental w
  calc bdry1 Nsub (foxVec Nsub w)
      = proj Nsub (∑ i : α, fox i w * (grp (FreeGroup.of i) - 1)) := by
        rw [bdry1, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, map_sub, proj_grp, map_one, foxVec]
    _ = 0 := by rw [h, map_sub, proj_grp_of_mem Nsub hw, map_one, sub_self]

/-- **The Crowell exact sequence.**  A vector killed by `∂₁` is the Fox vector of an
element of `Ñ`; in topological terms, `H₁` of the `1`-skeleton of the cover is `Ñ^ab`. -/
theorem exists_mem_of_bdry1_eq_zero (c : α → CoverRing Nsub) (hc : bdry1 Nsub c = 0) :
    ∃ r ∈ Nsub, c = foxVec Nsub r := by
  classical
  set a : α → FreeGroupRing α := fun i => liftQ Nsub (c i) with ha
  have hproja : ∀ i, proj Nsub (a i) = c i := fun i => proj_liftQ Nsub (c i)
  set b : FreeGroupRing α := ∑ i : α, a i * (grp (FreeGroup.of i) - 1) with hb
  have haug : aug b = 0 := by
    rw [hb, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mul, map_sub, aug_grp, map_one, sub_self, mul_zero]
  have hprojb : proj Nsub b = 0 := by
    rw [hb, map_sum]
    rw [← hc, bdry1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_sub, proj_grp, map_one, hproja]
  have hfoxb : foxProj Nsub b = c := by
    funext j
    have hterm : ∀ i : α, foxLin j (a i * (grp (FreeGroup.of i) - 1))
        = a i * (if j = i then 1 else 0) := by
      intro i
      rw [foxLin_mul, map_sub, aug_grp, map_one, sub_self, zero_smul, zero_add, map_sub]
      have h1 : foxLin j (1 : FreeGroupRing α) = 0 := by
        rw [← grp_one, foxLin_grp, fox_one]
      rw [h1, foxLin_grp, fox_of, sub_zero]
    have hsum : foxLin j b = a j := by
      rw [hb, map_sum, Finset.sum_congr rfl (fun i _ => hterm i)]
      simp
    rw [foxProj, hsum, hproja]
  have := foxProj_mem_foxMod Nsub b hprojb
  rw [hfoxb] at this
  exact this

/-- **The cycles of the cover are exactly the Fox vectors of the elements of `Ñ`.** -/
theorem bdry1_eq_zero_iff (c : α → CoverRing Nsub) :
    bdry1 Nsub c = 0 ↔ ∃ r ∈ Nsub, c = foxVec Nsub r := by
  refine ⟨exists_mem_of_bdry1_eq_zero Nsub c, ?_⟩
  rintro ⟨r, hr, rfl⟩
  exact bdry1_foxVec Nsub hr

/-- `H̃₀(K_N) = 0`: the image of `∂₁` is the augmentation ideal. -/
theorem exists_bdry1_preimage (z : CoverRing Nsub) (hz : augQ Nsub z = 0) :
    ∃ c : α → CoverRing Nsub, bdry1 Nsub c = z := by
  refine ⟨fun i => proj Nsub (foxLin i (liftQ Nsub z)), ?_⟩
  have haug : aug (liftQ Nsub z) = 0 := by
    rw [← augQ_proj Nsub, proj_liftQ, hz]
  have hfund := foxLin_fundamental (liftQ Nsub z)
  rw [haug, zero_smul, sub_zero] at hfund
  calc bdry1 Nsub (fun i => proj Nsub (foxLin i (liftQ Nsub z)))
      = proj Nsub (∑ i : α, foxLin i (liftQ Nsub z) * (grp (FreeGroup.of i) - 1)) := by
        rw [bdry1, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, map_sub, proj_grp, map_one]
    _ = z := by rw [hfund, proj_liftQ]

/-! ### The second boundary and the homology of the cover -/

variable {J : Type*} [Fintype J] (ρ : J → FreeGroup α)

/-- The boundary `∂₂ : ℤ[Q]^m → ℤ[Q]^n`, `∂₂(e_j) = (π(∂r_j/∂x_i))_i`. -/
noncomputable def bdry2 (u : J → CoverRing Nsub) : α → CoverRing Nsub :=
  fun i => ∑ j : J, u j * proj Nsub (fox i (ρ j))

omit [Fintype α] in
theorem bdry2_apply_eq (u : J → CoverRing Nsub) :
    bdry2 Nsub ρ u = ∑ j : J, u j • foxVec Nsub (ρ j) := by
  funext i
  simp [bdry2, foxVec, Finset.sum_apply]

omit [Fintype α] in
theorem bdry2_add (u v : J → CoverRing Nsub) :
    bdry2 Nsub ρ (u + v) = bdry2 Nsub ρ u + bdry2 Nsub ρ v := by
  funext i
  simp [bdry2, add_mul, Finset.sum_add_distrib]

omit [Fintype α] in
theorem bdry2_neg (u : J → CoverRing Nsub) :
    bdry2 Nsub ρ (-u) = - bdry2 Nsub ρ u := by
  funext i
  simp [bdry2, neg_mul, Finset.sum_neg_distrib]

omit [Fintype α] in
theorem bdry2_zero : bdry2 Nsub ρ 0 = 0 := by
  funext i; simp [bdry2]

omit [Fintype α] in
theorem bdry2_smul (v : CoverRing Nsub) (u : J → CoverRing Nsub) :
    bdry2 Nsub ρ (fun j => v * u j) = v • bdry2 Nsub ρ u := by
  funext i
  simp [bdry2, Finset.mul_sum, mul_assoc]

/-- The composite of the two boundaries vanishes: this is a chain complex. -/
theorem bdry1_bdry2 (hρ : ∀ j, ρ j ∈ Nsub) (u : J → CoverRing Nsub) :
    bdry1 Nsub (bdry2 Nsub ρ u) = 0 := by
  have hfund : ∀ j : J,
      ∑ i : α, proj Nsub (fox i (ρ j)) * (qgrp Nsub (FreeGroup.of i) - 1) = 0 := by
    intro j
    have h := fox_fundamental (ρ j)
    calc ∑ i : α, proj Nsub (fox i (ρ j)) * (qgrp Nsub (FreeGroup.of i) - 1)
        = proj Nsub (∑ i : α, fox i (ρ j) * (grp (FreeGroup.of i) - 1)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul, map_sub, proj_grp, map_one]
      _ = 0 := by rw [h, map_sub, proj_grp_of_mem Nsub (hρ j), map_one, sub_self]
  calc bdry1 Nsub (bdry2 Nsub ρ u)
      = ∑ j : J, u j * ∑ i : α, proj Nsub (fox i (ρ j)) * (qgrp Nsub (FreeGroup.of i) - 1) := by
        simp only [bdry1, bdry2, Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
    _ = 0 := by simp [hfund]

/-- If `N` is perfect then `ker ∂₁ ⊆ im ∂₂`, that is `H₁(K_N) = 0`. -/
theorem exists_bdry2_preimage (hρ : ∀ j, ρ j ∈ Nsub)
    (hperf : Nsub ≤ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅Nsub, Nsub⁆)
    (c : α → CoverRing Nsub) (hc : bdry1 Nsub c = 0) :
    ∃ u : J → CoverRing Nsub, bdry2 Nsub ρ u = c := by
  classical
  obtain ⟨r, hr, rfl⟩ := exists_mem_of_bdry1_eq_zero Nsub c hc
  -- the words whose Fox vector is a boundary form a normal subgroup
  let T : Subgroup (FreeGroup α) :=
    { carrier := {w | w ∈ Nsub ∧ ∃ u : J → CoverRing Nsub, bdry2 Nsub ρ u = foxVec Nsub w}
      one_mem' := ⟨Subgroup.one_mem _, 0, by rw [bdry2_zero, foxVec_one]⟩
      mul_mem' := by
        rintro v w ⟨hv, u₁, hu₁⟩ ⟨hw, u₂, hu₂⟩
        exact ⟨Subgroup.mul_mem _ hv hw, u₁ + u₂, by
          rw [bdry2_add, hu₁, hu₂, foxVec_mul hv]⟩
      inv_mem' := by
        rintro w ⟨hw, u, hu⟩
        exact ⟨Subgroup.inv_mem _ hw, -u, by rw [bdry2_neg, hu, foxVec_inv hw]⟩ }
  have hTnormal : T.Normal := by
    constructor
    rintro w ⟨hw, u, hu⟩ f
    refine ⟨Subgroup.Normal.conj_mem ‹Nsub.Normal› w hw f, fun j => proj Nsub (grp f) * u j, ?_⟩
    rw [bdry2_smul, hu, foxVec_conj hw]
  have hrange : Set.range ρ ⊆ (T : Set (FreeGroup α)) := by
    rintro _ ⟨j, rfl⟩
    refine ⟨hρ j, fun k => if k = j then 1 else 0, ?_⟩
    funext i
    simp [bdry2, foxVec]
  have hcomm : ⁅Nsub, Nsub⁆ ≤ T := by
    rw [Subgroup.commutator_le]
    intro v hv w hw
    have hvw : ⁅v, w⁆ ∈ Nsub := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hv hw)
        (Subgroup.inv_mem _ hv)) (Subgroup.inv_mem _ hw)
    refine ⟨hvw, 0, ?_⟩
    rw [bdry2_zero]
    have hcomm' : ⁅v, w⁆ = v * w * v⁻¹ * w⁻¹ := commutatorElement_def v w
    rw [hcomm', foxVec_mul (Subgroup.mul_mem _ (Subgroup.mul_mem _ hv hw) (Subgroup.inv_mem _ hv)),
      foxVec_mul (Subgroup.mul_mem _ hv hw), foxVec_mul hv, foxVec_inv hv, foxVec_inv hw]
    abel
  have hsub : Nsub ≤ T := by
    refine hperf.trans (sup_le ?_ hcomm)
    exact Subgroup.normalClosure_le_normal hrange
  exact (hsub hr).2

/-- **Acyclicity of the cover.**  If the relators lie in `Ñ`, if `N` is perfect and if
`∂₂` is injective (the requirements (2.2) of Section 2), then the chain complex of `K_N`
is acyclic: `H₂ = H₁ = H̃₀ = 0`. -/
theorem cover_acyclic (hρ : ∀ j, ρ j ∈ Nsub)
    (hperf : Nsub ≤ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅Nsub, Nsub⁆)
    (hinj : ∀ u : J → CoverRing Nsub, bdry2 Nsub ρ u = 0 → u = 0) :
    (∀ u : J → CoverRing Nsub, bdry1 Nsub (bdry2 Nsub ρ u) = 0) ∧
      (∀ u : J → CoverRing Nsub, bdry2 Nsub ρ u = 0 → u = 0) ∧
      (∀ c : α → CoverRing Nsub, bdry1 Nsub c = 0 →
        ∃ u : J → CoverRing Nsub, bdry2 Nsub ρ u = c) ∧
      (∀ z : CoverRing Nsub, augQ Nsub z = 0 → ∃ c : α → CoverRing Nsub, bdry1 Nsub c = z) ∧
      (∀ c : α → CoverRing Nsub, augQ Nsub (bdry1 Nsub c) = 0) :=
  ⟨bdry1_bdry2 Nsub ρ hρ, hinj, exists_bdry2_preimage Nsub ρ hρ hperf,
    exists_bdry1_preimage Nsub, augQ_bdry1 Nsub⟩

end FiniteChains
