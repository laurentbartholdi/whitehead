module

public import RequestProject.BlockFamilyB1Finsupp

@[expose] public section

/-! The triangular two-chain isomorphism for simultaneous slides over a
fixed core. Both the family and the core may have infinitely many cells.
Each input chain uses finitely many of the finite correction columns.

-/

noncomputable section

namespace FiniteChains
open BlockFamily

universe u
variable {C S I R : Type u} [Ring R]

@[simp] theorem fsOldOneIncl_single (c : C) (a : R) :
    fsOldOneIncl (Z := S) (Finsupp.single c a) = Finsupp.single (Sum.inl c) a := by
  classical
  ext i
  cases i <;> simp [Finsupp.single_apply]

/-- The off-diagonal correction has values entirely in the retained core. -/
def coreSlideCorrection (lam : S → C →₀ R) :
    ((C ⊕ S) →₀ R) →ₗ[R] ((C ⊕ S) →₀ R) :=
  Finsupp.linearCombination R
    (Sum.elim (fun _ : C => 0) (fun s => fsOldOneIncl (lam s)))

@[simp] theorem coreSlideCorrection_single_inl (lam : S → C →₀ R) (c : C) (a : R) :
    coreSlideCorrection lam (Finsupp.single (Sum.inl c) a) = 0 := by
  simp [coreSlideCorrection]

@[simp] theorem coreSlideCorrection_single_inr (lam : S → C →₀ R) (s : S) (a : R) :
    coreSlideCorrection lam (Finsupp.single (Sum.inr s) a) = a • fsOldOneIncl (lam s) := by
  simp [coreSlideCorrection]

theorem coreSlideCorrection_core (lam : S → C →₀ R) (x : C →₀ R) :
    coreSlideCorrection lam (fsOldOneIncl x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | single c a => rw [fsOldOneIncl_single, coreSlideCorrection_single_inl]

theorem coreSlideCorrection_square (lam : S → C →₀ R) (x : (C ⊕ S) →₀ R) :
    coreSlideCorrection lam (coreSlideCorrection lam x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | single c a =>
      cases c with
      | inl c => simp
      | inr s =>
          rw [coreSlideCorrection_single_inr, map_smul, coreSlideCorrection_core, smul_zero]

def coreSlideForward (lam : S → C →₀ R) :
    ((C ⊕ S) →₀ R) →ₗ[R] ((C ⊕ S) →₀ R) :=
  LinearMap.id - coreSlideCorrection lam

def coreSlideReverse (lam : S → C →₀ R) :
    ((C ⊕ S) →₀ R) →ₗ[R] ((C ⊕ S) →₀ R) :=
  LinearMap.id + coreSlideCorrection lam

@[simp] theorem coreSlideForward_reverse (lam : S → C →₀ R) (x : (C ⊕ S) →₀ R) :
    coreSlideForward lam (coreSlideReverse lam x) = x := by
  simp only [coreSlideForward, coreSlideReverse, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.id_apply, map_add, coreSlideCorrection_square]
  abel

@[simp] theorem coreSlideReverse_forward (lam : S → C →₀ R) (x : (C ⊕ S) →₀ R) :
    coreSlideReverse lam (coreSlideForward lam x) = x := by
  simp only [coreSlideForward, coreSlideReverse, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.id_apply, map_sub, coreSlideCorrection_square]
  abel

/-- The actual simultaneous slide is a chain-coordinate isomorphism;
no infinite composition of elementary slides is needed. -/
def coreSlideEquiv (lam : S → C →₀ R) :
    ((C ⊕ S) →₀ R) ≃ₗ[R] ((C ⊕ S) →₀ R) where
  toFun := coreSlideForward lam
  invFun := coreSlideReverse lam
  left_inv := coreSlideReverse_forward lam
  right_inv := coreSlideForward_reverse lam
  map_add' := map_add _
  map_smul' := map_smul _

/-- A column calculation suffices for the simultaneous boundary identity. -/
theorem coreSlide_boundary (lam : S → C →₀ R)
    (old new : ((C ⊕ S) →₀ R) →ₗ[R] (I →₀ R))
    (hcore : ∀ c, new (Finsupp.single (Sum.inl c) 1) = old (Finsupp.single (Sum.inl c) 1))
    (hextra : ∀ s, new (Finsupp.single (Sum.inr s) 1) =
      old (Finsupp.single (Sum.inr s) 1) + old (fsOldOneIncl (lam s)))
    (x : (C ⊕ S) →₀ R) : new x = old (coreSlideReverse lam x) := by
  have hm : new = old.comp (coreSlideReverse lam) := by
    apply Finsupp.lhom_ext
    intro k a
    rw [← Finsupp.smul_single_one k a, map_smul, map_smul]
    congr 1
    cases k with
    | inl c => simpa [coreSlideReverse] using hcore c
    | inr s => simpa [coreSlideReverse, map_add] using hextra s
  exact LinearMap.congr_fun hm x

theorem coreSlide_cycle_forward (lam : S → C →₀ R)
    (old new : ((C ⊕ S) →₀ R) →ₗ[R] (I →₀ R))
    (hboundary : ∀ x, new x = old (coreSlideReverse lam x))
    {x : (C ⊕ S) →₀ R} (hx : old x = 0) : new (coreSlideForward lam x) = 0 := by
  rw [hboundary, coreSlideReverse_forward, hx]

theorem coreSlide_cycle_preimage (lam : S → C →₀ R)
    (old new : ((C ⊕ S) →₀ R) →ₗ[R] (I →₀ R))
    (hboundary : ∀ x, new x = old (coreSlideReverse lam x))
    {x : (C ⊕ S) →₀ R} (hx : new x = 0) :
    old (coreSlideReverse lam x) = 0 ∧
      coreSlideForward lam (coreSlideReverse lam x) = x :=
  ⟨(hboundary x).symm.trans hx, coreSlideForward_reverse lam x⟩

theorem coreSlideForward_aug_zero (lam : S → C →₀ R) (ε : R →+* ℤ)
    (x : (C ⊕ S) →₀ R) (hx : ∀ k, ε (x k) = 0) (j : C ⊕ S) :
    ε (coreSlideForward lam x j) = 0 := by
  have hc : ε (coreSlideCorrection lam x j) = 0 := by
    rw [coreSlideCorrection, Finsupp.linearCombination_apply, Finsupp.sum_apply,
      map_finsuppSum]
    apply Finset.sum_eq_zero
    intro k hk
    change ε (x k * _) = 0
    rw [map_mul, hx k, zero_mul]
  change ε (x j - coreSlideCorrection lam x j) = 0
  rw [map_sub, hx j, hc, sub_self]

end FiniteChains
