module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.SingularChainMaps

@[expose] public section

/-! # The alternating-sum cancellation in a prism, in every dimension -/


namespace FiniteChains.SingularPrism

variable {V : Type*} [AddCommGroup V]

def altSum {n : ℕ} (f : Fin n → V) : V := ∑ i, (-1 : ℤ) ^ i.val • f i

theorem altSum_add {n : ℕ} (f g : Fin n → V) :
    altSum (fun i => f i + g i) = altSum f + altSum g := by
  simp only [altSum, smul_add, Finset.sum_add_distrib]

theorem altSum_sub {n : ℕ} (f g : Fin n → V) :
    altSum (fun i => f i - g i) = altSum f - altSum g := by
  simp only [altSum, smul_sub, Finset.sum_sub_distrib]

theorem altSum_succ {n : ℕ} (f : Fin (n + 1) → V) :
    altSum f = f 0 - altSum (fun i : Fin n => f i.succ) := by
  rw [altSum, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg_one,
    neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg, altSum]

theorem altSum_comm {m n : ℕ} (f : Fin m → Fin n → V) :
    altSum (fun i => altSum (f i)) = altSum (fun j => altSum (fun i => f i j)) := by
  simp only [altSum, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  congr 1
  funext j
  congr 1
  funext i
  rw [mul_comm]

def side {n : ℕ} (A : Fin (n + 1) → Fin (n + 2) → V) (i : Fin n) (j : Fin (n + 1)) : V :=
  if j ≤ i.castSucc then A i.succ j.castSucc else A i.castSucc j.succ

omit [AddCommGroup V] in
theorem side_zero_zero {n : ℕ} (A : Fin (n + 2) → Fin (n + 3) → V) :
    side A 0 0 = A 1 0 := by simp [side]

omit [AddCommGroup V] in
theorem side_zero_succ {n : ℕ} (A : Fin (n + 2) → Fin (n + 3) → V) (j : Fin (n + 1)) :
    side A 0 j.succ = A 0 j.succ.succ := by
  simp [side, Fin.le_def]

omit [AddCommGroup V] in
theorem side_succ_zero {n : ℕ} (A : Fin (n + 2) → Fin (n + 3) → V) (i : Fin n) :
    side A i.succ 0 = A i.succ.succ 0 := by simp [side]

omit [AddCommGroup V] in
theorem side_succ_succ {n : ℕ} (A : Fin (n + 2) → Fin (n + 3) → V)
    (i : Fin n) (j : Fin (n + 1)) :
    side A i.succ j.succ = side (fun i j => A i.succ j.succ) i j := by
  simp only [side, Fin.le_def, Fin.val_succ, Fin.val_castSucc, Nat.add_le_add_iff_right]
  rfl

theorem prism_cancellation (n : ℕ) (A : Fin (n + 1) → Fin (n + 2) → V)
    (hd : ∀ i : Fin n, A i.castSucc i.succ.castSucc = A i.succ i.succ.castSucc) :
    altSum (fun i => altSum (A i)) + altSum (fun i => altSum (side A i)) =
      A 0 0 - A (Fin.last n) (Fin.last (n + 1)) := by
  induction n with
  | zero =>
    simp [altSum, Fin.sum_univ_two, sub_eq_add_neg]
  | succ n ih =>
    let D : Fin (n + 1) → Fin (n + 2) → V := fun i j => A i.succ j.succ
    have hdD : ∀ i : Fin n, D i.castSucc i.succ.castSucc = D i.succ i.succ.castSucc := by
      intro i
      exact hd i.succ
    have hi := ih D hdD
    have hrow0 : altSum (A 0) = A 0 0 - A 0 1 +
        altSum (fun j : Fin (n + 1) => A 0 j.succ.succ) := by
      rw [altSum_succ, altSum_succ]
      simp only [Fin.succ_zero_eq_one]
      abel
    have hrow (i : Fin (n + 1)) : altSum (A i.succ) = A i.succ 0 - altSum (D i) :=
      altSum_succ _
    have hA : altSum (fun i => altSum (A i)) = A 0 0 - A 0 1 +
        altSum (fun j : Fin (n + 1) => A 0 j.succ.succ) -
        altSum (fun i : Fin (n + 1) => A i.succ 0) + altSum (fun i => altSum (D i)) := by
      rw [altSum_succ, hrow0]
      simp_rw [hrow]
      rw [altSum_sub]
      abel
    have hbrow0 : altSum (side A 0) = A 1 0 -
        altSum (fun j : Fin (n + 1) => A 0 j.succ.succ) := by
      rw [altSum_succ, side_zero_zero]
      simp only [side_zero_succ]
    have hbrow (i : Fin n) : altSum (side A i.succ) =
        A i.succ.succ 0 - altSum (side D i) := by
      rw [altSum_succ, side_succ_zero]
      simp only [side_succ_succ]
      rfl
    have hB : altSum (fun i => altSum (side A i)) =
        altSum (fun i : Fin (n + 1) => A i.succ 0) -
        altSum (fun j : Fin (n + 1) => A 0 j.succ.succ) + altSum (fun i => altSum (side D i)) := by
      rw [altSum_succ, hbrow0]
      simp_rw [hbrow]
      rw [altSum_sub, altSum_succ (fun i : Fin (n + 1) => A i.succ 0)]
      simp only [Fin.succ_zero_eq_one]
      abel
    rw [hA, hB]
    calc
      _ = A 0 0 - A 0 1 +
          (altSum (fun i => altSum (D i)) + altSum (fun i => altSum (side D i))) := by abel
      _ = A 0 0 - A 0 1 + (D 0 0 - D (Fin.last n) (Fin.last (n + 1))) := by rw [hi]
      _ = A 0 0 - A (Fin.last (n + 1)) (Fin.last (n + 2)) := by
        have hm : A 0 1 = A 1 1 := hd 0
        change A 0 0 - A 0 1 + (A 1 1 - A (Fin.last (n + 1)) (Fin.last (n + 2))) = _
        rw [hm]
        abel

end FiniteChains.SingularPrism
