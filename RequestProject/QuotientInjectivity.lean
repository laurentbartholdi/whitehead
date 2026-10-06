module

public import Mathlib

@[expose] public section

/-!
# Injectivity detected by a quotient (Lemma 2.1)

Lemma 2.1 of the paper states: if `H ◁ Q` is torsion-free abelian and
`f : U → V` is a map of free left `ℤ[Q]`-modules whose reduction along
`ℤ[Q] → ℤ[Q/H]` is injective, then `f` is injective; likewise over `𝔽ₚ`.

After restricting scalars to the *commutative* domain `R = k[H]` the statement
becomes the purely commutative-algebra fact formalized here: for a ring
homomorphism `ε : R →+* S` between commutative domains, coefficientwise
reduction along `ε` detects injectivity of maps between free modules, with no
finiteness assumption on the ranks.  This is exactly the elementary proof
sketched in the paper ("Outline of a direct proof"): one chooses a coordinate
functional with `ε`-nonzero value and induces on the size of a finite family.

The group-theoretic reduction (`k[Q]` is free over `k[H]` on coset
representatives, and `k[Q/H] ⊗_{k[Q]} U ≅ k ⊗_{k[H]} U`) is *not* formalized
here; it is what the ring homomorphism `ε` of the statements below stands for.
-/

namespace FiniteChains

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]

/-- Coefficientwise reduction of a finitely supported vector along a ring map. -/
noncomputable def reduceVec (ε : R →+* S) {κ : Type*} (v : κ →₀ R) : κ →₀ S :=
  Finsupp.mapRange ε ε.map_zero v

omit [IsDomain R] [IsDomain S] in
@[simp] theorem reduceVec_apply (ε : R →+* S) {κ : Type*} (v : κ →₀ R) (k : κ) :
    reduceVec ε v k = ε (v k) := rfl

omit [IsDomain R] [IsDomain S] in
theorem reduceVec_smul (ε : R →+* S) {κ : Type*} (a : R) (v : κ →₀ R) :
    reduceVec ε (a • v) = ε a • reduceVec ε v := by
  ext k; simp

omit [IsDomain R] [IsDomain S] in
theorem reduceVec_sub (ε : R →+* S) {κ : Type*} (v w : κ →₀ R) :
    reduceVec ε (v - w) = reduceVec ε v - reduceVec ε w := by
  ext k; simp

/-- **Independence is detected after reduction.**  If a finite family of vectors in a free
module over a commutative domain `R` becomes linearly independent after coefficientwise
reduction along `ε : R →+* S` to a commutative domain `S`, then the family was already
linearly independent over `R`. -/
theorem eq_zero_of_reduction_indep {κ ι : Type*} (ε : R →+* S)
    (T : Finset ι) (v : ι → (κ →₀ R))
    (hred : ∀ d : ι → S, (∑ j ∈ T, d j • reduceVec ε (v j)) = 0 → ∀ j ∈ T, d j = 0)
    (c : ι → R) (hc : (∑ j ∈ T, c j • v j) = 0) : ∀ j ∈ T, c j = 0 := by
  classical
  have key : ∀ T : Finset ι, ∀ v : ι → (κ →₀ R),
      (∀ d : ι → S, (∑ j ∈ T, d j • reduceVec ε (v j)) = 0 → ∀ j ∈ T, d j = 0) →
      ∀ c : ι → R, (∑ j ∈ T, c j • v j) = 0 → ∀ j ∈ T, c j = 0 := by
    intro T
    induction T using Finset.strongInduction with
    | _ T ih =>
      intro v hred c hc j₀ hj₀
      set T' : Finset ι := T.erase j₀ with hT'
      -- the reduced vector `v̄ j₀` is nonzero, so some coordinate survives `ε`
      have hv₀ : ∃ k : κ, ε (v j₀ k) ≠ 0 := by
        by_contra hall
        push_neg at hall
        have hzero : reduceVec ε (v j₀) = 0 := by
          ext k; simpa using hall k
        have hsum : (∑ j ∈ T, (if j = j₀ then (1 : S) else 0) • reduceVec ε (v j)) = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          by_cases hj : j = j₀
          · subst hj; simp [hzero]
          · simp [hj]
        have := hred (fun j => if j = j₀ then (1 : S) else 0) hsum j₀ hj₀
        simp at this
      obtain ⟨k, hk⟩ := hv₀
      set a : R := v j₀ k with ha
      have ha0 : a ≠ 0 := fun h => hk (by rw [h, map_zero])
      -- the modified family
      set w : ι → (κ →₀ R) := fun j => a • v j - (v j k) • v j₀ with hw
      have hwj₀ : w j₀ = 0 := by simp [hw, ha]
      -- reduced independence of the modified family
      have hred' : ∀ d : ι → S, (∑ j ∈ T', d j • reduceVec ε (w j)) = 0 → ∀ j ∈ T', d j = 0 := by
        intro d hd j hj
        set e : ι → S := fun j =>
          if j = j₀ then -(∑ j ∈ T', d j * ε (v j k)) else d j * ε a with he
        have hsplit : (∑ j ∈ T, e j • reduceVec ε (v j)) = 0 := by
          have hcalc : (∑ j ∈ T', d j • reduceVec ε (w j))
              = (∑ j ∈ T', (d j * ε a) • reduceVec ε (v j))
                - (∑ j ∈ T', d j * ε (v j k)) • reduceVec ε (v j₀) := by
            rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hw]
            simp only [reduceVec_sub, reduceVec_smul, smul_sub, smul_smul]
          have h1 : e j₀ = -(∑ j ∈ T', d j * ε (v j k)) := by simp [he]
          have h3 : (∑ j ∈ T.erase j₀, e j • reduceVec ε (v j))
              = ∑ j ∈ T', (d j * ε a) • reduceVec ε (v j) :=
            Finset.sum_congr rfl fun j hj' => by
              rw [show e j = d j * ε a by simp [he, Finset.ne_of_mem_erase hj']]
          rw [← Finset.add_sum_erase T (fun j => e j • reduceVec ε (v j)) hj₀, h1, h3, neg_smul, ← sub_eq_neg_add, ← hcalc, hd]
        have hj0 : j ∈ T := Finset.mem_of_mem_erase hj
        have := hred e hsplit j hj0
        rw [he] at this
        simp only [Finset.ne_of_mem_erase hj, if_false] at this
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd h hk
      -- the coefficients satisfy the corresponding relation for the modified family
      have hcw : (∑ j ∈ T', c j • w j) = 0 := by
        have hsplit : c j₀ • v j₀ + ∑ j ∈ T', c j • v j = 0 := by
          rw [hT', Finset.add_sum_erase T (fun j => c j • v j) hj₀]; exact hc
        have hsum1 : (∑ j ∈ T', c j • v j) = (-c j₀) • v j₀ := by
          rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]; exact hsplit
        have hcoord : (∑ j ∈ T', c j * (v j k)) = -(c j₀ * a) := by
          have := congrArg (fun x : κ →₀ R => x k) hsum1
          simpa [Finset.sum_apply', ha] using this
        have hcalc : (∑ j ∈ T', c j • w j)
            = a • (∑ j ∈ T', c j • v j) - (∑ j ∈ T', c j * (v j k)) • v j₀ := by
          rw [Finset.smul_sum, Finset.sum_smul, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hw]
          simp only [smul_sub, smul_smul]
          rw [mul_comm (c j) a]
        rw [hcalc, hsum1, hcoord, smul_smul, neg_smul, sub_neg_eq_add, ← add_smul]
        have : a * -c j₀ + c j₀ * a = 0 := by ring
        rw [this, zero_smul]
      -- induction on the smaller family
      have hsub : T' ⊂ T := Finset.erase_ssubset hj₀
      have hzero' : ∀ j ∈ T', c j = 0 := ih T' hsub w hred' c hcw
      -- only the `j₀` term survives, and evaluating at `k` finishes the proof
      have honly : c j₀ • v j₀ = 0 := by
        have hsplit : c j₀ • v j₀ + ∑ j ∈ T', c j • v j = 0 := by
          rw [hT', Finset.add_sum_erase T (fun j => c j • v j) hj₀]; exact hc
        have : (∑ j ∈ T', c j • v j) = 0 := by
          refine Finset.sum_eq_zero fun j hj => ?_
          rw [hzero' j hj, zero_smul]
        rwa [this, add_zero] at hsplit
      have := congrArg (fun x : κ →₀ R => x k) honly
      simp only [Finsupp.smul_apply, Finsupp.coe_zero, Pi.zero_apply, smul_eq_mul] at this
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h ha0
  exact key T v hred c hc

/-- The reduction along `ε : R →+* S` of an `R`-linear map between free modules. -/
noncomputable def reduceMap (ε : R →+* S) {ι κ : Type*}
    (f : (ι →₀ R) →ₗ[R] (κ →₀ R)) : (ι →₀ S) →ₗ[S] (κ →₀ S) :=
  Finsupp.lsum S fun i =>
    LinearMap.toSpanSingleton S (κ →₀ S) (reduceVec ε (f (Finsupp.single i 1)))

omit [IsDomain R] [IsDomain S] in
@[simp] theorem reduceMap_single (ε : R →+* S) {ι κ : Type*}
    (f : (ι →₀ R) →ₗ[R] (κ →₀ R)) (i : ι) (s : S) :
    reduceMap ε f (Finsupp.single i s) = s • reduceVec ε (f (Finsupp.single i 1)) := by
  simp [reduceMap, LinearMap.toSpanSingleton_apply]

/-- **Lemma 2.1, module-theoretic core.**  Reduction along a ring homomorphism between
commutative domains detects injectivity of maps between free modules of arbitrary rank. -/
theorem injective_of_reduceMap_injective (ε : R →+* S) {ι κ : Type*}
    (f : (ι →₀ R) →ₗ[R] (κ →₀ R)) (h : Function.Injective (reduceMap ε f)) :
    Function.Injective f := by
  classical
  rw [injective_iff_map_eq_zero]
  intro u hu
  -- the reduced images of the relevant basis vectors are independent
  set v : ι → (κ →₀ R) := fun i => f (Finsupp.single i 1) with hv
  have hred : ∀ d : ι → S, (∑ j ∈ u.support, d j • reduceVec ε (v j)) = 0 →
      ∀ j ∈ u.support, d j = 0 := by
    intro d hd j hj
    have hmap : reduceMap ε f (∑ j ∈ u.support, Finsupp.single j (d j)) = 0 := by
      rw [map_sum]
      simpa [hv] using hd
    have hzero : (∑ j ∈ u.support, Finsupp.single j (d j)) = 0 := by
      have := h (by simpa using hmap : reduceMap ε f (∑ j ∈ u.support, Finsupp.single j (d j))
        = reduceMap ε f 0)
      simpa using this
    have := congrArg (fun x : ι →₀ S => x j) hzero
    simpa [Finset.sum_apply', Finsupp.single_apply, Finset.sum_ite_eq' u.support j, hj] using this
  -- the coefficients of `u` satisfy the corresponding relation
  have hc : (∑ j ∈ u.support, u j • v j) = 0 := by
    have hu' : u = ∑ j ∈ u.support, Finsupp.single j (u j) := (Finsupp.sum_single u).symm
    calc (∑ j ∈ u.support, u j • v j)
        = f (∑ j ∈ u.support, Finsupp.single j (u j)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hv]
          simp [← LinearMap.map_smul, Finsupp.smul_single]
      _ = f u := by rw [← hu']
      _ = 0 := hu
  have hzero := eq_zero_of_reduction_indep ε u.support v hred u hc
  ext j
  by_cases hj : j ∈ u.support
  · simpa using hzero j hj
  · simpa using Finsupp.notMem_support_iff.mp hj

end FiniteChains
