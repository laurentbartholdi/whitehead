module

public import RequestProject.Cockcroft
public import RequestProject.AbelianElimination
public import RequestProject.FoxNaturality
public import RequestProject.InitialPair
public import RequestProject.Pi2Dictionary

@[expose] public section

/-!
# The initial Cockcroft pair `D ⊂ Y_D` of Lemma 3.1

Let `D` be given by a finite presentation `⟨x_i (i ∈ I) | r_j (j ∈ J)⟩` with exponent-sum
matrix `M`.  Lemma 3.1 of the paper builds the complex

  `Y_D = ⟨x_i, a_i, b_i | r_j, x_i[a_i,b_i]⁻¹, [a_i,a_k], [a_i,b_k], [b_i,a_k], [b_i,b_k]⟩`
                                                                            `(i < k)`

and proves: `G(Y_D) = ⊕_i (ℤ a_i ⊕ ℤ b_i)`, the complex `Y_D` is Cockcroft, and the
inclusion `D ⊂ Y_D` kills `π₁(D)` and is zero on `π₂`.

This file carries out the whole of Lemma 3.1 inside the combinatorial model of the project:
`Y_D` is the presentation `FiniteChains.relY` on the generators `FiniteChains.GenY` and the
two-cells `FiniteChains.CellY`, `π₂` is the module of Fox cycles and the Cockcroft property
is `FiniteChains.IsCockcroft` (see `RequestProject/Cockcroft.lean`).

The paper obtains the Cockcroft property of `Y_D` from a comparison with a torus, using
`π₂(torus) = 0` and naturality of the Hurewicz map.  Here it is proved directly: a Fox
cycle is evaluated by the homomorphism `ℤ[G] → ℤ^{(I × Bool)}` induced by
`G(Y_D) → ⊕_i (ℤ a_i ⊕ ℤ b_i)`, which kills products of elements of the augmentation ideal.
That evaluation makes the cycle equations at the generators `a_i, b_i` force the
coefficients of the cells `x_i[a_i,b_i]⁻¹` and of the cross-commutators to have zero
augmentation, and the cycle equations at the generators `x_i` then say that the remaining
augmentation vector is killed by `M`, hence is zero because `D` is acyclic.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra
open scoped commutatorElement IsMulCommutative

universe u

variable {I J : Type u}

/-- The generators of `Y_D`: the generators `x_i` of `D` (`Sum.inl i`) and the two added
generators `a_i = y_{i,false}`, `b_i = y_{i,true}` (`Sum.inr (i, s)`). -/
abbrev GenY (I : Type u) : Type u := I ⊕ (I × Bool)

/-- The index set of the cross-commutators `[y_{i,s}, y_{k,t}]`, one for each pair `i < k`
and each pair of signs. -/
abbrev CrossY (I : Type u) [LinearOrder I] : Type u := {p : I × I // p.1 < p.2} × Bool × Bool

/-- The two-cells of `Y_D`: the relators `r_j` of `D`, the new relators `x_i[a_i,b_i]⁻¹`,
and the cross-commutators. -/
abbrev CellY (I J : Type u) [LinearOrder I] : Type u := J ⊕ (I ⊕ CrossY I)

/-- The generator `x_i` of `Y_D`. -/
def xGen (i : I) : FreeGroup (GenY I) := FreeGroup.of (Sum.inl i)

/-- The generator `a_i` (`s = false`) or `b_i` (`s = true`) of `Y_D`. -/
def yGen (i : I) (s : Bool) : FreeGroup (GenY I) := FreeGroup.of (Sum.inr (i, s))

variable [LinearOrder I]

/-- The relators of `Y_D`. -/
def relY (r : J → FreeGroup I) : CellY I J → FreeGroup (GenY I)
  | Sum.inl j => FreeGroup.map Sum.inl (r j)
  | Sum.inr (Sum.inl i) => xGen i * ⁅yGen i false, yGen i true⁆⁻¹
  | Sum.inr (Sum.inr (⟨p, _⟩, s, t)) => ⁅yGen p.1 s, yGen p.2 t⁆

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] (r : J → FreeGroup I)

/-- The fundamental group `G(Y_D)` of the complex `Y_D`. -/
abbrev GroupY : Type u := PresGroup (relY r)

/-- The image of `x_i` in `G(Y_D)`. -/
def xEl (i : I) : GroupY r := QuotientGroup.mk (xGen i)

/-- The image of `a_i`, `b_i` in `G(Y_D)`. -/
def yEl (i : I) (s : Bool) : GroupY r := QuotientGroup.mk (yGen i s)

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem mk_relY (c : CellY I J) : (QuotientGroup.mk (relY r c) : GroupY r) = 1 := by
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.subset_normalClosure ⟨c, rfl⟩

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- The cross-commutators: generators with a smaller and a larger index commute. -/
theorem commute_yEl_of_lt {i k : I} (hik : i < k) (s t : Bool) :
    Commute (yEl r i s) (yEl r k t) := by
  have h : (QuotientGroup.mk (relY r (Sum.inr (Sum.inr (⟨(i, k), hik⟩, s, t)))) : GroupY r) = 1 :=
    mk_relY r _
  have hrel : relY r (Sum.inr (Sum.inr (⟨(i, k), hik⟩, s, t))) = ⁅yGen i s, yGen k t⁆ := rfl
  rw [hrel] at h
  have hmap : (QuotientGroup.mk ⁅yGen i s, yGen k t⁆ : GroupY r)
      = ⁅yEl r i s, yEl r k t⁆ :=
    map_commutatorElement (QuotientGroup.mk' (relSub (relY r))) _ _
  rw [hmap] at h
  exact commutatorElement_eq_one_iff_commute.1 h

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- The cross-commutators: generators with different indices commute in `G(Y_D)`. -/
theorem commute_yEl_of_ne {i k : I} (hik : i ≠ k) (s t : Bool) :
    Commute (yEl r i s) (yEl r k t) := by
  rcases lt_or_gt_of_ne hik with h | h
  · exact commute_yEl_of_lt r h s t
  · exact (commute_yEl_of_lt r h t s).symm

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- The relator `x_i[a_i,b_i]⁻¹`: in `G(Y_D)` one has `x_i = [a_i, b_i]`. -/
theorem xEl_eq_commutator (i : I) : xEl r i = ⁅yEl r i false, yEl r i true⁆ := by
  have h : (QuotientGroup.mk' (relSub (relY r))) (xGen i * ⁅yGen i false, yGen i true⁆⁻¹) = 1 :=
    mk_relY r (Sum.inr (Sum.inl i))
  rw [map_mul, map_inv, map_commutatorElement] at h
  exact mul_inv_eq_one.1 h

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- The homomorphism `π₁(D) → G(Y_D)` induced by the inclusion, on the level of free
groups. -/
theorem lift_xEl (w : FreeGroup I) :
    FreeGroup.lift (fun i => xEl r i) w = (QuotientGroup.mk (FreeGroup.map Sum.inl w) : GroupY r) := by
  have h : FreeGroup.lift (fun i => xEl r i)
      = ((QuotientGroup.mk' (relSub (relY r))).comp (FreeGroup.map Sum.inl)) := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    simp [FreeGroup.lift_apply_of, xEl, xGen]
  exact congrArg (fun f : FreeGroup I →* GroupY r => f w) h

/-- Surjectivity of the exponent-sum matrix of `D` — part of the acyclicity of `D`. -/
def ExpSurjective : Prop := Function.Surjective (Finsupp.linearCombination ℤ (expCol r))

variable {r}

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- **The elimination step of Lemma 3.1.**  If the exponent-sum matrix of `D` is surjective,
then `[a_i, b_i] = 1` in `G(Y_D)`. -/
theorem commutator_yEl_eq_one (hM : ExpSurjective r) (i : I) :
    ⁅yEl r i false, yEl r i true⁆ = 1 := by
  have hab : CrossCommuting (fun i => yEl r i false) (fun i => yEl r i true) := by
    intro i k hik
    exact ⟨commute_yEl_of_ne r hik false false, commute_yEl_of_ne r hik false true,
      commute_yEl_of_ne r hik true false, commute_yEl_of_ne r hik true true⟩
  have hu : ∀ i k : I, Commute (⁅yEl r i false, yEl r i true⁆) (⁅yEl r k false, yEl r k true⁆) :=
    fun i k => commute_pairComm _ _ hab i k
  have hlift : FreeGroup.lift (fun i => ⁅yEl r i false, yEl r i true⁆)
      = FreeGroup.lift (fun i => xEl r i) := by
    refine congrArg _ (funext fun i => ?_)
    exact (xEl_eq_commutator r i).symm
  have hrel : ∀ j, FreeGroup.lift (fun i => ⁅yEl r i false, yEl r i true⁆) (r j) = 1 := by
    intro j
    rw [hlift, lift_xEl r]
    exact mk_relY r (Sum.inl j)
  exact eq_one_of_expCol_surjective _ hu r hrel hM i

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- **The inclusion `D ⊂ Y_D` kills `π₁(D)`**: every generator `x_i` of `D` becomes trivial
in `G(Y_D)`. -/
theorem xEl_eq_one (hM : ExpSurjective r) (i : I) : xEl r i = 1 := by
  rw [xEl_eq_commutator, commutator_yEl_eq_one hM]

omit [Fintype I] [Fintype J] [DecidableEq J] in
/-- **All added generators commute** in `G(Y_D)`. -/
theorem commute_yEl (hM : ExpSurjective r) (i k : I) (s t : Bool) :
    Commute (yEl r i s) (yEl r k t) := by
  by_cases hik : i = k
  · subst hik
    have hc := commutatorElement_eq_one_iff_commute.mp (commutator_yEl_eq_one hM i)
    cases s <;> cases t <;>
      first
        | exact Commute.refl _
        | exact hc
        | exact hc.symm
  · exact commute_yEl_of_ne r hik s t

/-! ### The Fox matrix of `Y_D` -/

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- The image of a word of `D` in `G(Y_D)` is trivial. -/
theorem mk_map_inl (hM : ExpSurjective r) (w : FreeGroup I) :
    (QuotientGroup.mk (FreeGroup.map Sum.inl w) : GroupY r) = 1 := by
  rw [← lift_xEl r w]
  have h : FreeGroup.lift (fun i => xEl r i) = (1 : FreeGroup I →* GroupY r) := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    rw [FreeGroup.lift_apply_of, xEl_eq_one hM i]
    rfl
  rw [h]
  rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- The image in `ℤ[G(Y_D)]` of an element of the group ring of `D` is its augmentation. -/
theorem proj_freeRingMap_inl (hM : ExpSurjective r) (z : FreeGroupRing I) :
    proj (relSub (relY r)) (freeRingMap Sum.inl z) = (aug z) • (1 : MonoidAlgebra ℤ (GroupY r)) := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, add_smul]
  | single w n =>
      have h1 : freeRingMap Sum.inl (MonoidAlgebra.single w n : FreeGroupRing I)
          = (MonoidAlgebra.single (FreeGroup.map Sum.inl w) n : FreeGroupRing (GenY I)) := by
        change MonoidAlgebra.mapDomain (FreeGroup.map Sum.inl) (MonoidAlgebra.single w n) = _
        exact MonoidAlgebra.mapDomain_single
      rw [h1, proj_single, mk_map_inl hM w, aug_single]
      show MonoidAlgebra.single (1 : GroupY r) n = n • (MonoidAlgebra.single 1 1)
      rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]

/-- The image of the group element `y_{i,s}` in the group ring `ℤ[G(Y_D)]`. -/
noncomputable def yRing (i : I) (s : Bool) : MonoidAlgebra ℤ (GroupY r) :=
  MonoidAlgebra.of ℤ (GroupY r) (yEl r i s)

/-- The Fox derivative of a commutator of two free generators. -/
theorem fox_commutator_free {β : Type*} [DecidableEq β] (A B g : β) :
    fox g ⁅FreeGroup.of A, FreeGroup.of B⁆
      = (if g = A then (1 : FreeGroupRing β)
            - grp (FreeGroup.of A * FreeGroup.of B * (FreeGroup.of A)⁻¹) else 0)
        + (if g = B then grp (FreeGroup.of A)
            - grp ⁅FreeGroup.of A, FreeGroup.of B⁆ else 0) := by
  rcases eq_or_ne A B with rfl | hAB
  · have h1 : ⁅FreeGroup.of A, FreeGroup.of A⁆ = 1 := by simp
    have h2 : FreeGroup.of A * FreeGroup.of A * (FreeGroup.of A)⁻¹ = FreeGroup.of A := by group
    rw [h1, h2, fox_one]
    by_cases hA : g = A <;> simp [hA]
  · show fox g (FreeGroup.of A * FreeGroup.of B * (FreeGroup.of A)⁻¹ * (FreeGroup.of B)⁻¹) = _
    rw [fox_mul, fox_mul, fox_mul, fox_inv, fox_inv, fox_of, fox_of]
    by_cases hA : g = A <;> by_cases hB : g = B <;>
      simp [hA, hB, hAB, hAB.symm, grp_mul, commutatorElement_def] <;> noncomm_ring

/-- The Fox derivative of a commutator of two free generators, read in a quotient in which
the two images commute. -/
theorem proj_fox_commutator {β : Type*} [DecidableEq β] (Nsub : Subgroup (FreeGroup β))
    [Nsub.Normal] (A B g : β)
    (hcomm : Commute (QuotientGroup.mk (FreeGroup.of A) : FreeGroup β ⧸ Nsub)
      (QuotientGroup.mk (FreeGroup.of B))) :
    proj Nsub (fox g ⁅FreeGroup.of A, FreeGroup.of B⁆)
      = (if g = A then 1 - qgrp Nsub (FreeGroup.of B) else 0)
        + (if g = B then qgrp Nsub (FreeGroup.of A) - 1 else 0) := by
  have hconj : (QuotientGroup.mk (FreeGroup.of A * FreeGroup.of B * (FreeGroup.of A)⁻¹)
      : FreeGroup β ⧸ Nsub) = QuotientGroup.mk (FreeGroup.of B) := by
    show (QuotientGroup.mk' Nsub) (FreeGroup.of A * FreeGroup.of B * (FreeGroup.of A)⁻¹)
      = (QuotientGroup.mk' Nsub) (FreeGroup.of B)
    rw [map_mul, map_mul, map_inv]
    simp only [QuotientGroup.mk'_apply]
    rw [hcomm.eq, mul_inv_cancel_right]
  have hcom1 : (QuotientGroup.mk ⁅FreeGroup.of A, FreeGroup.of B⁆ : FreeGroup β ⧸ Nsub) = 1 := by
    show (QuotientGroup.mk' Nsub) ⁅FreeGroup.of A, FreeGroup.of B⁆ = 1
    rw [map_commutatorElement]
    simp only [QuotientGroup.mk'_apply]
    exact commutatorElement_eq_one_iff_commute.2 hcomm
  have hq1 : qgrp Nsub (FreeGroup.of A * FreeGroup.of B * (FreeGroup.of A)⁻¹)
      = qgrp Nsub (FreeGroup.of B) :=
    congrArg (fun q => MonoidAlgebra.single q (1 : ℤ)) hconj
  have hq2 : qgrp Nsub ⁅FreeGroup.of A, FreeGroup.of B⁆ = 1 := by
    unfold qgrp
    rw [hcom1]
    rfl
  rw [fox_commutator_free, map_add, apply_ite (proj Nsub), apply_ite (proj Nsub),
    map_zero, map_sub, map_sub, map_one, proj_grp, proj_grp, proj_grp, hq1, hq2]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem yRing_eq_qgrp (i : I) (s : Bool) :
    yRing (r := r) i s
      = qgrp (relSub (relY r)) (FreeGroup.of (Sum.inr (i, s)) : FreeGroup (GenY I)) := rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- In `G(Y_D)` the generators `x_k` are trivial, so they are trivial in the group ring. -/
theorem qgrp_xGen (hM : ExpSurjective r) (k : I) :
    qgrp (relSub (relY r)) (FreeGroup.of (Sum.inl k) : FreeGroup (GenY I)) = 1 := by
  have h : (QuotientGroup.mk (FreeGroup.of (Sum.inl k) : FreeGroup (GenY I)) : GroupY r) = 1 :=
    xEl_eq_one hM k
  unfold qgrp
  rw [h]
  rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- The commutator `[a_k, b_k]` is trivial in `G(Y_D)`. -/
theorem qgrp_comm_inv (hM : ExpSurjective r) (k : I) :
    qgrp (relSub (relY r)) (⁅(FreeGroup.of (Sum.inr (k, false)) : FreeGroup (GenY I)),
      FreeGroup.of (Sum.inr (k, true))⁆⁻¹) = 1 := by
  have h : (QuotientGroup.mk (⁅(FreeGroup.of (Sum.inr (k, false)) : FreeGroup (GenY I)),
      FreeGroup.of (Sum.inr (k, true))⁆⁻¹) : GroupY r) = 1 := by
    show (QuotientGroup.mk' (relSub (relY r)))
      (⁅(FreeGroup.of (Sum.inr (k, false)) : FreeGroup (GenY I)),
        FreeGroup.of (Sum.inr (k, true))⁆⁻¹) = 1
    rw [map_inv, map_commutatorElement, inv_eq_one]
    exact commutator_yEl_eq_one hM k
  unfold qgrp
  rw [h]
  rfl

omit [Fintype I] [Fintype J] [DecidableEq J] in
/-- The Fox matrix of `Y_D` at an old generator and an old two-cell: the exponent-sum
matrix of `D`. -/
theorem foxMatrix_inl_inl (hM : ExpSurjective r) (i : I) (j : J) :
    foxMatrixPres (relY r) (Sum.inl i) (Sum.inl j)
      = (expEntry r i j) • (1 : MonoidAlgebra ℤ (GroupY r)) := by
  show proj (relSub (relY r)) (fox (Sum.inl i) (FreeGroup.map Sum.inl (r j))) = _
  rw [fox_map Sum.inl Sum.inl_injective, proj_freeRingMap_inl hM, aug_fox]
  rfl

omit [Fintype I] [Fintype J] [DecidableEq J] in
/-- The Fox matrix of `Y_D` at a new generator and an old two-cell vanishes. -/
theorem foxMatrix_inr_inl (i : I) (s : Bool) (j : J) :
    foxMatrixPres (relY r) (Sum.inr (i, s)) (Sum.inl j) = 0 := by
  show proj (relSub (relY r)) (fox (Sum.inr (i, s)) (FreeGroup.map Sum.inl (r j))) = 0
  rw [fox_map_of_not_mem_range Sum.inl (fun k => by simp), map_zero]

omit [Fintype I] [Fintype J] [DecidableEq J] in
/-- The Fox matrix of `Y_D` at an old generator and a cell `x_k[a_k,b_k]⁻¹`. -/
theorem foxMatrix_inl_mid (hM : ExpSurjective r) (i k : I) :
    foxMatrixPres (relY r) (Sum.inl i) (Sum.inr (Sum.inl k))
      = if k = i then 1 else 0 := by
  show proj (relSub (relY r)) (fox (Sum.inl i)
    ((FreeGroup.of (Sum.inl k) : FreeGroup (GenY I)) *
      ⁅FreeGroup.of (Sum.inr (k, false)), FreeGroup.of (Sum.inr (k, true))⁆⁻¹)) = _
  have hcomm : proj (relSub (relY r)) (fox (Sum.inl i)
      ⁅(FreeGroup.of (Sum.inr (k, false)) : FreeGroup (GenY I)),
        FreeGroup.of (Sum.inr (k, true))⁆) = 0 := by
    rw [proj_fox_commutator (relSub (relY r)) (Sum.inr (k, false)) (Sum.inr (k, true))
      (Sum.inl i) (commute_yEl hM k k false true)]
    simp
  rw [fox_mul, fox_inv, map_add, map_mul, map_neg, map_mul, hcomm, mul_zero, neg_zero,
    mul_zero, add_zero]
  show proj (relSub (relY r)) (fox (Sum.inl i) (FreeGroup.of (Sum.inl k))) = _
  rw [fox_of, apply_ite (proj (relSub (relY r))), map_one, map_zero]
  by_cases hik : k = i
  · subst hik
    simp
  · simp [hik, Ne.symm hik]

omit [Fintype I] [Fintype J] [DecidableEq J] in
/-- The Fox matrix of `Y_D` at a new generator and a cell `x_k[a_k,b_k]⁻¹`. -/
theorem foxMatrix_inr_mid (hM : ExpSurjective r) (i k : I) (s : Bool) :
    foxMatrixPres (relY r) (Sum.inr (i, s)) (Sum.inr (Sum.inl k))
      = if k = i then (if s then -(yRing (r := r) i false - 1) else yRing (r := r) i true - 1) else 0 := by
  show proj (relSub (relY r)) (fox (Sum.inr (i, s))
    ((FreeGroup.of (Sum.inl k) : FreeGroup (GenY I)) *
      ⁅FreeGroup.of (Sum.inr (k, false)), FreeGroup.of (Sum.inr (k, true))⁆⁻¹)) = _
  have hx : proj (relSub (relY r))
      (fox (Sum.inr (i, s)) (FreeGroup.of (Sum.inl k) : FreeGroup (GenY I))) = 0 := by
    rw [fox_of, if_neg (by simp), map_zero]
  have hcomm := proj_fox_commutator (relSub (relY r)) (Sum.inr (k, false)) (Sum.inr (k, true))
    (Sum.inr (i, s)) (commute_yEl hM k k false true)
  rw [fox_mul, fox_inv, map_add, map_mul, map_neg, map_mul, hx, zero_add, proj_grp,
    qgrp_xGen hM, one_mul, proj_grp, qgrp_comm_inv hM, one_mul, hcomm]
  rw [← yRing_eq_qgrp, ← yRing_eq_qgrp]
  by_cases hik : k = i
  · subst hik
    cases s <;> simp
  · have hne : ∀ b : Bool, (Sum.inr (i, s) : GenY I) ≠ Sum.inr (k, b) := by
      intro b h
      rw [Sum.inr.injEq, Prod.mk.injEq] at h
      exact hik h.1.symm
    rw [if_neg hik, if_neg (hne false), if_neg (hne true)]
    simp

omit [Fintype I] [Fintype J] [DecidableEq J] in
/-- The Fox matrix of `Y_D` at an old generator and a cross-commutator vanishes. -/
theorem foxMatrix_inl_cross (hM : ExpSurjective r) (i : I) (c : CrossY I) :
    foxMatrixPres (relY r) (Sum.inl i) (Sum.inr (Sum.inr c)) = 0 := by
  obtain ⟨⟨⟨p, q⟩, hpq⟩, s, t⟩ := c
  show proj (relSub (relY r)) (fox (Sum.inl i)
    ⁅(FreeGroup.of (Sum.inr (p, s)) : FreeGroup (GenY I)), FreeGroup.of (Sum.inr (q, t))⁆) = 0
  rw [proj_fox_commutator (relSub (relY r)) (Sum.inr (p, s)) (Sum.inr (q, t))
    (Sum.inl i) (commute_yEl hM p q s t)]
  simp

omit [Fintype I] [Fintype J] [DecidableEq J] in
/-- The Fox matrix of `Y_D` at a new generator and a cross-commutator. -/
theorem foxMatrix_inr_cross (hM : ExpSurjective r) (i : I) (s : Bool) (c : CrossY I) :
    foxMatrixPres (relY r) (Sum.inr (i, s)) (Sum.inr (Sum.inr c))
      = (if (i, s) = (c.1.1.1, c.2.1) then 1 - yRing (r := r) c.1.1.2 c.2.2 else 0)
        + (if (i, s) = (c.1.1.2, c.2.2) then yRing (r := r) c.1.1.1 c.2.1 - 1 else 0) := by
  obtain ⟨⟨⟨p, q⟩, hpq⟩, u, v⟩ := c
  show proj (relSub (relY r)) (fox (Sum.inr (i, s))
    ⁅(FreeGroup.of (Sum.inr (p, u)) : FreeGroup (GenY I)), FreeGroup.of (Sum.inr (q, v))⁆) = _
  rw [proj_fox_commutator (relSub (relY r)) (Sum.inr (p, u)) (Sum.inr (q, v))
    (Sum.inr (i, s)) (commute_yEl hM p q u v), ← yRing_eq_qgrp, ← yRing_eq_qgrp]
  simp [Prod.ext_iff]

/-! ### The evaluation homomorphism -/

variable (r)

/-- The homomorphism of the free group onto `⊕_i (ℤ a_i ⊕ ℤ b_i)` used in Lemma 3.1: the
generators `x_i` go to `0` and the generators `a_i, b_i` to the corresponding basis
vectors. -/
noncomputable def thetaFree : FreeGroup (GenY I) →* Multiplicative (I × Bool →₀ ℤ) :=
  FreeGroup.lift fun g =>
    match g with
    | Sum.inl _ => 1
    | Sum.inr P => Multiplicative.ofAdd (Finsupp.single P (1 : ℤ))

omit [LinearOrder I] [Fintype I] [DecidableEq I] in
theorem thetaFree_map_inl (w : FreeGroup I) :
    thetaFree (FreeGroup.map Sum.inl w) = 1 := by
  have h : thetaFree.comp (FreeGroup.map (Sum.inl : I → GenY I))
      = (1 : FreeGroup I →* Multiplicative (I × Bool →₀ ℤ)) := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    show thetaFree (FreeGroup.of (Sum.inl i)) = 1
    rw [thetaFree, FreeGroup.lift_apply_of]
  exact congrArg (fun f : FreeGroup I →* Multiplicative (I × Bool →₀ ℤ) => f w) h

omit [Fintype J] [DecidableEq J] in
omit [Fintype I] [DecidableEq I] in
theorem thetaFree_relY (c : CellY I J) : thetaFree (relY r c) = 1 := by
  match c with
  | Sum.inl j => exact thetaFree_map_inl (r j)
  | Sum.inr (Sum.inl i) =>
      show thetaFree ((FreeGroup.of (Sum.inl i) : FreeGroup (GenY I)) *
        ⁅FreeGroup.of (Sum.inr (i, false)), FreeGroup.of (Sum.inr (i, true))⁆⁻¹) = 1
      rw [map_mul, map_inv, map_commutatorElement,
        commutatorElement_eq_one_iff_commute.2 (Commute.all _ _)]
      simp [thetaFree, FreeGroup.lift_apply_of]
  | Sum.inr (Sum.inr ⟨⟨(p, q), hpq⟩, u, v⟩) =>
      show thetaFree ⁅(FreeGroup.of (Sum.inr (p, u)) : FreeGroup (GenY I)),
        FreeGroup.of (Sum.inr (q, v))⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.2 (Commute.all _ _)

/-- The homomorphism `G(Y_D) → ⊕_i (ℤ a_i ⊕ ℤ b_i)` of Lemma 3.1. -/
noncomputable def thetaY : GroupY r →* Multiplicative (I × Bool →₀ ℤ) :=
  QuotientGroup.lift (relSub (relY r)) thetaFree
    (by
      have hsub : relSub (relY r) ≤ thetaFree.ker := by
        refine Subgroup.normalClosure_le_normal ?_
        rintro _ ⟨c, rfl⟩
        exact thetaFree_relY r c
      exact fun w hw => hsub hw)

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem thetaY_yEl (i : I) (s : Bool) :
    Multiplicative.toAdd (thetaY r (yEl r i s)) = Finsupp.single (i, s) 1 := by
  show Multiplicative.toAdd (thetaFree (FreeGroup.of (Sum.inr (i, s)) : FreeGroup (GenY I)))
    = Finsupp.single (i, s) 1
  rw [thetaFree, FreeGroup.lift_apply_of]
  rfl

/-- The coordinate functional `ℤ[G(Y_D)] → ℤ` attached to a generator `y_P`: the
composition of `thetaY` with the `P`-th coordinate.  It kills products of two elements of
the augmentation ideal, which is what makes the cycle equations computable. -/
noncomputable def psiY (P : I × Bool) : MonoidAlgebra ℤ (GroupY r) →ₗ[ℤ] ℤ :=
  (Finsupp.linearCombination ℤ fun g : GroupY r => (Multiplicative.toAdd (thetaY r g)) P).comp
    (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem psiY_single (P : I × Bool) (g : GroupY r) (n : ℤ) :
    psiY r P (MonoidAlgebra.single g n) = n * (Multiplicative.toAdd (thetaY r g)) P := by
  show Finsupp.linearCombination ℤ
      (fun g : GroupY r => (Multiplicative.toAdd (thetaY r g)) P) (Finsupp.single g n) = _
  rw [Finsupp.linearCombination_single, smul_eq_mul]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- **The key computation.**  Evaluating `z · (g - 1)` returns the augmentation of `z`
times the `P`-th coordinate of the image of `g`; in particular products of two elements of
the augmentation ideal are killed. -/
theorem psiY_mul_group_sub_one (P : I × Bool) (g : GroupY r)
    (z : MonoidAlgebra ℤ (GroupY r)) :
    psiY r P (z * (MonoidAlgebra.of ℤ (GroupY r) g - 1))
      = augPres (relY r) z * (Multiplicative.toAdd (thetaY r g)) P := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add z₁ z₂ h₁ h₂ =>
      rw [add_mul, map_add, h₁, h₂, map_add, add_mul]
  | single h n =>
      have hmul : (MonoidAlgebra.single h n : MonoidAlgebra ℤ (GroupY r)) *
          (MonoidAlgebra.of ℤ (GroupY r) g - 1)
          = MonoidAlgebra.single (h * g) n - MonoidAlgebra.single h n := by
        rw [mul_sub, mul_one]
        congr 1
        show MonoidAlgebra.single h n * MonoidAlgebra.single g 1 = _
        rw [MonoidAlgebra.single_mul_single, mul_one]
      rw [hmul, map_sub, psiY_single, psiY_single, augQ_single]
      have hhom : Multiplicative.toAdd (thetaY r (h * g))
          = Multiplicative.toAdd (thetaY r h) + Multiplicative.toAdd (thetaY r g) := by
        rw [map_mul]
        rfl
      rw [hhom]
      simp [mul_add]

omit [Fintype I] [Fintype J] [DecidableEq J] in
theorem psiY_mul_sub_one (P Q : I × Bool) (z : MonoidAlgebra ℤ (GroupY r)) :
    psiY r P (z * (yRing (r := r) Q.1 Q.2 - 1)) = augPres (relY r) z * (if Q = P then 1 else 0) := by
  rw [show yRing (r := r) Q.1 Q.2 = MonoidAlgebra.of ℤ (GroupY r) (yEl r Q.1 Q.2) from rfl,
    psiY_mul_group_sub_one, thetaY_yEl]
  simp [Finsupp.single_apply]

omit [Fintype I] [Fintype J] [DecidableEq J] in
theorem psiY_mul_one_sub (P Q : I × Bool) (z : MonoidAlgebra ℤ (GroupY r)) :
    psiY r P (z * (1 - yRing (r := r) Q.1 Q.2)) = -(augPres (relY r) z * (if Q = P then 1 else 0)) := by
  have h : z * (1 - yRing (r := r) Q.1 Q.2) = -(z * (yRing (r := r) Q.1 Q.2 - 1)) := by noncomm_ring
  rw [h, map_neg, psiY_mul_sub_one]

/-! ### Lemma 3.1 -/

variable {r}

omit [Fintype I] [Fintype J] [DecidableEq J] in
/-- The contribution of a cross-commutator cell to the cycle equation at a generator
`y_{i,s}`, evaluated in the coordinate `P`. -/
theorem psiY_cross_term (hM : ExpSurjective r) (P : I × Bool) (i : I) (s : Bool)
    (c : CrossY I) (z : MonoidAlgebra ℤ (GroupY r)) :
    psiY r P (z * foxMatrixPres (relY r) (Sum.inr (i, s)) (Sum.inr (Sum.inr c)))
      = (if (i, s) = (c.1.1.1, c.2.1)
            then -(augPres (relY r) z * (if (c.1.1.2, c.2.2) = P then 1 else 0)) else 0)
        + (if (i, s) = (c.1.1.2, c.2.2)
            then augPres (relY r) z * (if (c.1.1.1, c.2.1) = P then 1 else 0) else 0) := by
  rw [foxMatrix_inr_cross hM, mul_add, map_add]
  congr 1
  · by_cases h : (i, s) = (c.1.1.1, c.2.1)
    · rw [if_pos h, if_pos h]
      exact psiY_mul_one_sub r P (c.1.1.2, c.2.2) z
    · rw [if_neg h, if_neg h, mul_zero, map_zero]
  · by_cases h : (i, s) = (c.1.1.2, c.2.2)
    · rw [if_pos h, if_pos h]
      exact psiY_mul_sub_one r P (c.1.1.1, c.2.1) z
    · rw [if_neg h, if_neg h, mul_zero, map_zero]

omit [DecidableEq J] in
/-- **The coefficients of the cells `x_i[a_i,b_i]⁻¹` in a Fox cycle have zero
augmentation.** -/
theorem aug_cycle_mid (hM : ExpSurjective r) {v : CellY I J → MonoidAlgebra ℤ (GroupY r)}
    (hv : IsFoxCycle (relY r) v) (i : I) :
    augPres (relY r) (v (Sum.inr (Sum.inl i))) = 0 := by
  classical
  have h := congrArg (psiY r (i, true)) (hv (Sum.inr (i, false)))
  rw [map_zero, map_sum, Fintype.sum_sum_type] at h
  rw [Fintype.sum_sum_type] at h
  -- the old cells contribute nothing
  have hold : ∑ j : J, psiY r (i, true)
      (v (Sum.inl j) * foxMatrixPres (relY r) (Sum.inr (i, false)) (Sum.inl j)) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [foxMatrix_inr_inl, mul_zero, map_zero]
  -- the cross-commutators contribute nothing
  have hcross : ∑ c : CrossY I, psiY r (i, true)
      (v (Sum.inr (Sum.inr c)) *
        foxMatrixPres (relY r) (Sum.inr (i, false)) (Sum.inr (Sum.inr c))) = 0 := by
    refine Finset.sum_eq_zero fun c _ => ?_
    obtain ⟨⟨⟨p, q⟩, hpq⟩, u, w⟩ := c
    rw [psiY_cross_term hM]
    have hlt : p < q := hpq
    have h1 : ((i, false) = (p, u)) → ((q, w) : I × Bool) ≠ (i, true) := by
      intro e1 e2
      have hp : p = i := (congrArg Prod.fst e1).symm
      have hq : q = i := congrArg Prod.fst e2
      rw [hp, hq] at hlt
      exact lt_irrefl _ hlt
    have h2 : ((i, false) = (q, w)) → ((p, u) : I × Bool) ≠ (i, true) := by
      intro e1 e2
      have hq : q = i := (congrArg Prod.fst e1).symm
      have hp : p = i := congrArg Prod.fst e2
      rw [hp, hq] at hlt
      exact lt_irrefl _ hlt
    by_cases hc1 : ((i, false) : I × Bool) = (p, u) <;> by_cases hc2 : ((i, false) : I × Bool) = (q, w)
    · rw [if_pos hc1, if_pos hc2, if_neg (h1 hc1), if_neg (h2 hc2)]
      simp
    · rw [if_pos hc1, if_neg hc2, if_neg (h1 hc1)]
      simp
    · rw [if_neg hc1, if_pos hc2, if_neg (h2 hc2)]
      simp
    · rw [if_neg hc1, if_neg hc2]
      simp
  -- the middle cells contribute the coefficient of the `i`-th cell
  have hmid : ∑ k : I, psiY r (i, true)
      (v (Sum.inr (Sum.inl k)) *
        foxMatrixPres (relY r) (Sum.inr (i, false)) (Sum.inr (Sum.inl k)))
      = augPres (relY r) (v (Sum.inr (Sum.inl i))) := by
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · rw [foxMatrix_inr_mid hM, if_pos rfl]
      show psiY r (i, true) (v (Sum.inr (Sum.inl i)) * (yRing (r := r) i true - 1)) = _
      rw [psiY_mul_sub_one r (i, true) (i, true)]
      simp
    · intro k _ hk
      rw [foxMatrix_inr_mid hM, if_neg hk, mul_zero, map_zero]
  rw [hold, hcross, hmid, zero_add, add_zero] at h
  exact h

omit [DecidableEq J] in
/-- **The coefficients of the cross-commutator cells in a Fox cycle have zero
augmentation.** -/
theorem aug_cycle_cross (hM : ExpSurjective r) {v : CellY I J → MonoidAlgebra ℤ (GroupY r)}
    (hv : IsFoxCycle (relY r) v) (c₀ : CrossY I) :
    augPres (relY r) (v (Sum.inr (Sum.inr c₀))) = 0 := by
  classical
  obtain ⟨⟨⟨p, q⟩, hpq⟩, u, w⟩ := c₀
  have h := congrArg (psiY r (q, w)) (hv (Sum.inr (p, u)))
  rw [map_zero, map_sum, Fintype.sum_sum_type] at h
  rw [Fintype.sum_sum_type] at h
  have hold : ∑ j : J, psiY r (q, w)
      (v (Sum.inl j) * foxMatrixPres (relY r) (Sum.inr (p, u)) (Sum.inl j)) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [foxMatrix_inr_inl, mul_zero, map_zero]
  have hmid : ∑ k : I, psiY r (q, w)
      (v (Sum.inr (Sum.inl k)) *
        foxMatrixPres (relY r) (Sum.inr (p, u)) (Sum.inr (Sum.inl k))) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [foxMatrix_inr_mid hM]
    by_cases hk : k = p
    · subst hk
      have hne : ((k, !u) : I × Bool) ≠ (q, w) := by
        intro hEq
        exact absurd (congrArg Prod.fst hEq ▸ hpq) (lt_irrefl _)
      rw [if_pos rfl]
      cases u
      · show psiY r (q, w) (v (Sum.inr (Sum.inl k)) * (yRing (r := r) k true - 1)) = 0
        rw [psiY_mul_sub_one r (q, w) (k, true), if_neg (by simpa using hne), mul_zero]
      · show psiY r (q, w) (v (Sum.inr (Sum.inl k)) * -(yRing (r := r) k false - 1)) = 0
        rw [mul_neg, map_neg, psiY_mul_sub_one r (q, w) (k, false),
          if_neg (by simpa using hne), mul_zero, neg_zero]
    · rw [if_neg hk, mul_zero, map_zero]
  have hcross : ∑ c : CrossY I, psiY r (q, w)
      (v (Sum.inr (Sum.inr c)) *
        foxMatrixPres (relY r) (Sum.inr (p, u)) (Sum.inr (Sum.inr c)))
      = -augPres (relY r) (v (Sum.inr (Sum.inr (⟨(p, q), hpq⟩, u, w)))) := by
    rw [Finset.sum_eq_single_of_mem (⟨(p, q), hpq⟩, u, w) (Finset.mem_univ _)]
    · have hlt : p < q := hpq
      have hne : ((p, u) : I × Bool) ≠ (q, w) := by
        intro hEq
        have hp : p = q := congrArg Prod.fst hEq
        rw [hp] at hlt
        exact lt_irrefl _ hlt
      rw [psiY_cross_term hM]
      simp [hne]
    · rintro ⟨⟨⟨p', q'⟩, hpq'⟩, u', w'⟩ _ hne
      rw [psiY_cross_term hM]
      have hfirst : ((p, u) : I × Bool) = (p', u') → ((q', w') : I × Bool) ≠ (q, w) := by
        intro h1 h2
        refine hne ?_
        obtain ⟨rfl, rfl⟩ : p = p' ∧ u = u' := ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩
        obtain ⟨rfl, rfl⟩ : q' = q ∧ w' = w := ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩
        rfl
      have hsecond : ((p, u) : I × Bool) = (q', w') → ((p', u') : I × Bool) ≠ (q, w) := by
        intro h1 h2
        have hq' : q' = p := (congrArg Prod.fst h1).symm
        have hp' : p' = q := congrArg Prod.fst h2
        rw [hp', hq'] at hpq'
        exact absurd (hpq.trans hpq') (lt_irrefl _)
      by_cases hc1 : ((p, u) : I × Bool) = (p', u') <;>
        by_cases hc2 : ((p, u) : I × Bool) = (q', w')
      · rw [if_pos hc1, if_pos hc2, if_neg (hfirst hc1), if_neg (hsecond hc2)]
        simp
      · rw [if_pos hc1, if_neg hc2, if_neg (hfirst hc1)]
        simp
      · rw [if_neg hc1, if_pos hc2, if_neg (hsecond hc2)]
        simp
      · rw [if_neg hc1, if_neg hc2]
        simp
  rw [hold, hmid, hcross, zero_add, zero_add] at h
  exact neg_eq_zero.1 h

omit [DecidableEq J] in
/-- **`Y_D` is Cockcroft** (Lemma 3.1), provided `D` is acyclic: its exponent-sum matrix is
injective and surjective. -/
theorem isCockcroft_relY (hMs : ExpSurjective r) (hMi : ExpInjective r) :
    IsCockcroft (relY r) := by
  classical
  intro v hv c
  match c with
  | Sum.inr (Sum.inl i) => exact aug_cycle_mid hMs hv i
  | Sum.inr (Sum.inr c₀) => exact aug_cycle_cross hMs hv c₀
  | Sum.inl j =>
      -- the cycle equations at the old generators say that the augmentation vector of the
      -- old coefficients is killed by the exponent-sum matrix of `D`
      refine hMi (fun j => augPres (relY r) (v (Sum.inl j))) (fun i => ?_) j
      have h := congrArg (augPres (relY r)) (hv (Sum.inl i))
      rw [map_zero, map_sum, Fintype.sum_sum_type] at h
      rw [Fintype.sum_sum_type] at h
      have hmid : ∑ k : I, augPres (relY r)
          (v (Sum.inr (Sum.inl k)) *
            foxMatrixPres (relY r) (Sum.inl i) (Sum.inr (Sum.inl k))) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [foxMatrix_inl_mid hMs]
        by_cases hk : k = i
        · subst hk
          rw [if_pos rfl, mul_one, aug_cycle_mid hMs hv k]
        · rw [if_neg hk, mul_zero, map_zero]
      have hcross : ∑ c : CrossY I, augPres (relY r)
          (v (Sum.inr (Sum.inr c)) *
            foxMatrixPres (relY r) (Sum.inl i) (Sum.inr (Sum.inr c))) = 0 := by
        refine Finset.sum_eq_zero fun c _ => ?_
        rw [foxMatrix_inl_cross hMs, mul_zero, map_zero]
      have hold : ∑ j : J, augPres (relY r)
          (v (Sum.inl j) * foxMatrixPres (relY r) (Sum.inl i) (Sum.inl j))
          = ∑ j : J, augPres (relY r) (v (Sum.inl j)) * expEntry r i j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, foxMatrix_inl_inl hMs]
        congr 1
        rw [map_zsmul, map_one, smul_eq_mul, mul_one]
      rw [hold, hmid, hcross, add_zero, add_zero] at h
      exact h

/-! ### The inclusion `D ⊂ Y_D` -/

variable (r)

/-- The homomorphism `π₁(D) → π₁(Y_D)` induced by the inclusion. -/
def presMapY : PresGroup r →* GroupY r :=
  QuotientGroup.map (relSub r) (relSub (relY r)) (FreeGroup.map Sum.inl) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    exact Subgroup.mem_comap.2 (Subgroup.subset_normalClosure ⟨Sum.inl j, rfl⟩))

variable {r}

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- **The inclusion `D ⊂ Y_D` kills `π₁(D)`.** -/
theorem presMapY_eq_one (hM : ExpSurjective r) (g : PresGroup r) : presMapY r g = 1 := by
  induction g using QuotientGroup.induction_on with
  | H w => exact mk_map_inl hM w

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- Because `π₁(D) → π₁(Y_D)` is trivial, the induced map of group rings is the
augmentation. -/
theorem mapDomainRingHom_presMapY (hM : ExpSurjective r) (z : MonoidAlgebra ℤ (PresGroup r)) :
    MonoidAlgebra.mapDomainRingHom ℤ (presMapY r) z
      = (augPres r z) • (1 : MonoidAlgebra ℤ (GroupY r)) := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add z₁ z₂ h₁ h₂ => rw [map_add, h₁, h₂, map_add, add_smul]
  | single g n =>
      have hmap : MonoidAlgebra.mapDomainRingHom ℤ (presMapY r)
          (MonoidAlgebra.single g n : MonoidAlgebra ℤ (PresGroup r))
          = MonoidAlgebra.single (presMapY r g) n := MonoidAlgebra.mapDomain_single
      rw [hmap, presMapY_eq_one hM, augQ_single]
      show MonoidAlgebra.single (1 : GroupY r) n = n • MonoidAlgebra.single 1 1
      rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]

/-- **The inclusion `D ⊂ Y_D` is zero on `π₂`** (Lemma 3.1), provided `D` is acyclic.  The
statement is the cellular one: the lift of the inclusion to the universal covers sends every
two-cycle of `D̃` to zero — exactly the hypothesis `zero_pi2` of a chain of presentation
complexes. -/
theorem zero_pi2_initial (hMs : ExpSurjective r) (hMi : ExpInjective r)
    (u : ((FreeGroup I ⧸ relSub r) × J) →₀ ℤ) (hu : Comb.bdry2 (Comb.univCover r) u = 0) :
    Finsupp.mapDomain (Prod.map (⇑(presMapY r)) (Sum.inl : J → CellY I J)) u = 0 := by
  refine (Comb.univCover_zero_pi2_iff r (presMapY r) (Sum.inl : J → CellY I J)
    Sum.inl_injective).2 ?_ u hu
  intro v hv
  refine (Comb.mapDomain_mapRange_eq_zero_iff (presMapY r) (Sum.inl : J → CellY I J)
    Sum.inl_injective v).2 ?_
  intro j
  have hcyc : IsFoxCycle r (fun c => v c) := by
    intro a
    rw [← sum_support_eq_sum_univ r v a]
    exact hv a
  have haug : augPres r (v j) = 0 := isCockcroft_of_expInjective r hMi (fun c => v c) hcyc j
  rw [mapDomainRingHom_presMapY hMs, haug, zero_smul]

/-! ### The fundamental group of `Y_D` -/

omit [Fintype I] [Fintype J] [DecidableEq J] in
theorem commute_genY (hM : ExpSurjective r) (a b : GenY I) :
    Commute (QuotientGroup.mk (FreeGroup.of a) : GroupY r)
      (QuotientGroup.mk (FreeGroup.of b)) := by
  rcases a with i | ⟨i, s⟩
  · rw [show (QuotientGroup.mk (FreeGroup.of (Sum.inl i) : FreeGroup (GenY I)) : GroupY r) = 1 from
      xEl_eq_one hM i]
    exact Commute.one_left _
  · rcases b with k | ⟨k, t⟩
    · rw [show (QuotientGroup.mk (FreeGroup.of (Sum.inl k) : FreeGroup (GenY I)) : GroupY r) = 1
        from xEl_eq_one hM k]
      exact Commute.one_right _
    · exact commute_yEl hM i k s t

omit [Fintype I] [Fintype J] [DecidableEq J] in
theorem commute_of_mk (hM : ExpSurjective r) (a : GenY I) (w : FreeGroup (GenY I)) :
    Commute (QuotientGroup.mk (FreeGroup.of a) : GroupY r) (QuotientGroup.mk w) := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of b => exact commute_genY hM a b
  | inv_of b ih =>
      have h : (QuotientGroup.mk ((FreeGroup.of b)⁻¹) : GroupY r)
          = (QuotientGroup.mk (FreeGroup.of b))⁻¹ := map_inv (QuotientGroup.mk' _) _
      rw [h]
      exact (commute_genY hM a b).inv_right
  | mul w₁ w₂ h₁ h₂ =>
      have h : (QuotientGroup.mk (w₁ * w₂) : GroupY r)
          = QuotientGroup.mk w₁ * QuotientGroup.mk w₂ := map_mul (QuotientGroup.mk' _) _ _
      rw [h]
      exact h₁.mul_right h₂

omit [Fintype I] [Fintype J] [DecidableEq J] in
theorem commute_mkY (hM : ExpSurjective r) (w w' : FreeGroup (GenY I)) :
    Commute (QuotientGroup.mk w : GroupY r) (QuotientGroup.mk w') := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of a => exact commute_of_mk hM a w'
  | inv_of a ih =>
      have h : (QuotientGroup.mk ((FreeGroup.of a)⁻¹) : GroupY r)
          = (QuotientGroup.mk (FreeGroup.of a))⁻¹ := map_inv (QuotientGroup.mk' _) _
      rw [h]
      exact (commute_of_mk hM a w').inv_left
  | mul w₁ w₂ h₁ h₂ =>
      have h : (QuotientGroup.mk (w₁ * w₂) : GroupY r)
          = QuotientGroup.mk w₁ * QuotientGroup.mk w₂ := map_mul (QuotientGroup.mk' _) _ _
      rw [h]
      exact h₁.mul_left h₂

omit [Fintype I] [Fintype J] [DecidableEq J] in
/-- **`G(Y_D)` is abelian** (Lemma 3.1). -/
theorem mul_comm_groupY (hM : ExpSurjective r) (g h : GroupY r) : g * h = h * g := by
  induction g using QuotientGroup.induction_on with
  | H w =>
      induction h using QuotientGroup.induction_on with
      | H w' => exact (commute_mkY hM w w').eq

/-- **`G(Y_D) = ⊕_i (ℤ a_i ⊕ ℤ b_i)`** (Lemma 3.1): the map sending `a_i, b_i` to the
corresponding basis vectors and `x_i` to `0` is an isomorphism onto the free abelian group
on the added pairs of generators. -/
noncomputable def groupYEquiv (hM : ExpSurjective r) :
    GroupY r ≃* Multiplicative (I × Bool →₀ ℤ) := by
  classical
  letI : CommGroup (GroupY r) :=
    { (inferInstance : Group (GroupY r)) with mul_comm := mul_comm_groupY hM }
  let f : (I × Bool →₀ ℤ) →+ Additive (GroupY r) :=
    Finsupp.liftAddHom fun P =>
      zmultiplesHom (Additive (GroupY r)) (Additive.ofMul (yEl r P.1 P.2))
  have hf_single : ∀ (P : I × Bool) (n : ℤ),
      Additive.toMul (f (Finsupp.single P n)) = yEl r P.1 P.2 ^ n := by
    intro P n
    show Additive.toMul (Finsupp.liftAddHom
      (fun P : I × Bool => zmultiplesHom (Additive (GroupY r))
        (Additive.ofMul (yEl r P.1 P.2))) (Finsupp.single P n)) = _
    rw [Finsupp.liftAddHom_apply_single]
    rfl
  let invHom : Multiplicative (I × Bool →₀ ℤ) →* GroupY r :=
    { toFun := fun m => Additive.toMul (f (Multiplicative.toAdd m))
      map_one' := by
        show Additive.toMul (f 0) = 1
        rw [map_zero]
        rfl
      map_mul' := fun m₁ m₂ => by
        show Additive.toMul (f (Multiplicative.toAdd m₁ + Multiplicative.toAdd m₂)) = _
        rw [map_add]
        rfl }
  have hleft : Function.LeftInverse invHom (thetaY r) := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H w =>
      have hcomp : (invHom.comp (thetaY r)).comp (QuotientGroup.mk' (relSub (relY r)))
          = (QuotientGroup.mk' (relSub (relY r))) := by
        refine FreeGroup.ext_hom _ _ fun a => ?_
        rcases a with i | ⟨i, s⟩
        · show invHom (thetaY r (QuotientGroup.mk (FreeGroup.of (Sum.inl i)))) = _
          rw [show (QuotientGroup.mk (FreeGroup.of (Sum.inl i) : FreeGroup (GenY I)) : GroupY r)
              = 1 from xEl_eq_one hM i, map_one, map_one]
          exact (xEl_eq_one hM i).symm
        · show invHom (thetaY r (yEl r i s)) = yEl r i s
          show Additive.toMul (f (Multiplicative.toAdd (thetaY r (yEl r i s)))) = yEl r i s
          rw [thetaY_yEl, hf_single, zpow_one]
      exact congrArg (fun F : FreeGroup (GenY I) →* GroupY r => F w) hcomp
  have hright : Function.RightInverse invHom (thetaY r) := by
    intro m
    have key : ∀ x : (I × Bool →₀ ℤ),
        Multiplicative.toAdd (thetaY r (Additive.toMul (f x))) = x := by
      intro x
      induction x using Finsupp.induction_linear with
      | zero =>
          rw [map_zero]
          show Multiplicative.toAdd (thetaY r 1) = 0
          rw [map_one]
          rfl
      | add x₁ x₂ h₁ h₂ =>
          rw [map_add]
          show Multiplicative.toAdd (thetaY r (Additive.toMul (f x₁) * Additive.toMul (f x₂))) = _
          rw [map_mul]
          show Multiplicative.toAdd (thetaY r (Additive.toMul (f x₁)))
            + Multiplicative.toAdd (thetaY r (Additive.toMul (f x₂))) = _
          rw [h₁, h₂]
      | single P n =>
          rw [hf_single, map_zpow]
          show n • Multiplicative.toAdd (thetaY r (yEl r P.1 P.2)) = _
          rw [thetaY_yEl, Finsupp.smul_single, smul_eq_mul, mul_one]
    exact key (Multiplicative.toAdd m)
  exact MulEquiv.mk ⟨thetaY r, invHom, hleft, hright⟩ (fun a b => map_mul (thetaY r) a b)

omit [Fintype I] [Fintype J] [DecidableEq J] in
/-- **`G(Y_D)` is free abelian on the added pairs of generators** (Lemma 3.1). -/
theorem nonempty_groupYEquiv (hM : ExpSurjective r) :
    Nonempty (GroupY r ≃* Multiplicative (I × Bool →₀ ℤ)) :=
  ⟨groupYEquiv hM⟩

end FiniteChains
