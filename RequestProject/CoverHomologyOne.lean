module

public import RequestProject.CoverChainComplex

@[expose] public section

/-!
# The boundaries of the cover are the Fox vectors of the relator subgroup

`RequestProject/CoverChainComplex.lean` identifies the cycles of the chain complex of the
cover `K_N` with the Fox vectors of the elements of `Ñ` (the Crowell exact sequence).  This
file identifies the boundaries: the image of `∂₂` consists exactly of the Fox vectors of
the elements of the normal closure `R = ⟪r_1, …, r_m⟫` of the relators.

Together the two statements describe the first homology of the cover completely:

  `H₁(K_N) = 0 ⟺ every element of Ñ has the Fox vector of an element of R`,

which is the algebraic form of `H₁(K_N) = N/[N, N]` up to the classical fact (Magnus) that
the Fox vector map has kernel exactly `[Ñ, Ñ]`.
-/

namespace FiniteChains

open MonoidAlgebra

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (Nsub : Subgroup (FreeGroup α)) [Nsub.Normal]
variable {J : Type*} [Fintype J] (ρ : J → FreeGroup α)

omit [Fintype α] in
/-- The boundary `∂₂` is the `ℤ[Q]`-combination of the Fox vectors of the relators. -/
theorem bdry2_eq_sum_smul (u : J → CoverRing Nsub) :
    bdry2 Nsub ρ u = ∑ j : J, u j • foxVec Nsub (ρ j) := by
  funext i
  rw [bdry2]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, foxVec]

variable {Nsub ρ}

omit [Fintype α] in
/-- A `ℤ[Q]`-multiple of the Fox vector of an element of a normal subgroup `P ≤ Ñ` is again
the Fox vector of an element of `P`. -/
theorem exists_mem_smul_foxVec {P : Subgroup (FreeGroup α)} [P.Normal] (hP : P ≤ Nsub)
    {r : FreeGroup α} (hr : r ∈ P) (x : CoverRing Nsub) :
    ∃ w ∈ P, x • foxVec Nsub r = foxVec Nsub w := by
  classical
  induction x using MonoidAlgebra.induction_linear with
  | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
  | add x₁ x₂ h₁ h₂ =>
      obtain ⟨w₁, hw₁, e₁⟩ := h₁
      obtain ⟨w₂, hw₂, e₂⟩ := h₂
      exact ⟨w₁ * w₂, Subgroup.mul_mem _ hw₁ hw₂, by
        rw [foxVec_mul (hP hw₁), ← e₁, ← e₂, add_smul]⟩
  | single q n =>
      obtain ⟨f, rfl⟩ := Quotient.exists_rep q
      have hconj : f * r * f⁻¹ ∈ P := Subgroup.Normal.conj_mem ‹P.Normal› r hr f
      refine ⟨(f * r * f⁻¹) ^ n, Subgroup.zpow_mem _ hconj n, ?_⟩
      have hsingle : (single (QuotientGroup.mk f : FreeGroup α ⧸ Nsub) n : CoverRing Nsub)
          = n • proj Nsub (grp f) := by
        rw [proj_grp, qgrp, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
      rw [foxVec_zpow (Nsub := Nsub) (hP hconj) n, foxVec_conj (Nsub := Nsub) (hP hr),
        hsingle, smul_assoc]

omit [Fintype α] in
/-- **Every boundary is the Fox vector of an element of the relator subgroup.** -/
theorem exists_mem_normalClosure_of_bdry2 (hρ : ∀ j, ρ j ∈ Nsub) (u : J → CoverRing Nsub) :
    ∃ w ∈ Subgroup.normalClosure (Set.range ρ), bdry2 Nsub ρ u = foxVec Nsub w := by
  classical
  set R := Subgroup.normalClosure (Set.range ρ) with hR
  have hRle : R ≤ Nsub := by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    exact hρ j
  have hmem : ∀ j, ρ j ∈ R := fun j =>
    Subgroup.subset_normalClosure (Set.mem_range_self j)
  have key : ∀ s : Finset J, ∃ w ∈ R, (∑ j ∈ s, u j • foxVec Nsub (ρ j)) = foxVec Nsub w := by
    intro s
    induction s using Finset.cons_induction with
    | empty => exact ⟨1, Subgroup.one_mem _, by simp⟩
    | cons j s hj ih =>
        obtain ⟨w, hw, hwe⟩ := ih
        obtain ⟨w', hw', hw'e⟩ := exists_mem_smul_foxVec hRle (hmem j) (u j)
        refine ⟨w' * w, Subgroup.mul_mem _ hw' hw, ?_⟩
        rw [Finset.sum_cons, hwe, hw'e, foxVec_mul (hRle hw')]
  obtain ⟨w, hw, hwe⟩ := key Finset.univ
  exact ⟨w, hw, by rw [bdry2_eq_sum_smul, hwe]⟩

variable (Nsub ρ)

omit [Fintype α] in
/-- **Every Fox vector of an element of the relator subgroup is a boundary.** -/
theorem exists_bdry2_of_mem_normalClosure (hρ : ∀ j, ρ j ∈ Nsub) {w : FreeGroup α}
    (hw : w ∈ Subgroup.normalClosure (Set.range ρ)) :
    ∃ u : J → CoverRing Nsub, bdry2 Nsub ρ u = foxVec Nsub w := by
  classical
  -- the words whose Fox vector is a boundary form a normal subgroup containing the relators
  let T : Subgroup (FreeGroup α) :=
    { carrier := {v | v ∈ Nsub ∧ ∃ u : J → CoverRing Nsub, bdry2 Nsub ρ u = foxVec Nsub v}
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
  exact ((Subgroup.normalClosure_le_normal hrange) hw).2

omit [Fintype α] in
/-- **The boundaries of the cover are exactly the Fox vectors of the relator subgroup.** -/
theorem bdry2_mem_range_iff (hρ : ∀ j, ρ j ∈ Nsub) (c : α → CoverRing Nsub) :
    (∃ u : J → CoverRing Nsub, bdry2 Nsub ρ u = c) ↔
      ∃ w ∈ Subgroup.normalClosure (Set.range ρ), c = foxVec Nsub w := by
  constructor
  · rintro ⟨u, rfl⟩
    exact exists_mem_normalClosure_of_bdry2 hρ u
  · rintro ⟨w, hw, rfl⟩
    exact exists_bdry2_of_mem_normalClosure Nsub ρ hρ hw

/-- **The first homology of the cover, explicitly.**  `H₁(K_N) = 0` if and only if every
element of `Ñ` has the same Fox vector as some element of the relator subgroup; by the
Crowell sequence the cycles are the Fox vectors of `Ñ` and the boundaries those of `R`. -/
theorem homologyOne_eq_zero_iff (hρ : ∀ j, ρ j ∈ Nsub) :
    (∀ c : α → CoverRing Nsub, bdry1 Nsub c = 0 →
        ∃ u : J → CoverRing Nsub, bdry2 Nsub ρ u = c) ↔
      ∀ w ∈ Nsub, ∃ r ∈ Subgroup.normalClosure (Set.range ρ),
        foxVec Nsub w = foxVec Nsub r := by
  constructor
  · intro h w hw
    obtain ⟨u, hu⟩ := h (foxVec Nsub w) (bdry1_foxVec Nsub hw)
    obtain ⟨r, hr, hre⟩ := exists_mem_normalClosure_of_bdry2 hρ u
    exact ⟨r, hr, by rw [← hu, hre]⟩
  · intro h c hc
    obtain ⟨w, hw, rfl⟩ := exists_mem_of_bdry1_eq_zero Nsub c hc
    obtain ⟨r, hr, hre⟩ := h w hw
    rw [hre]
    exact exists_bdry2_of_mem_normalClosure Nsub ρ hρ hr

end FiniteChains
