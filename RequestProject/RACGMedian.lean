import RequestProject.RACGDescent

/-!
# Medians in the Cayley graph of a right-angled Coxeter group

This file proves the combinatorial heart of Gromov's criterion for the cube complexes used in
the paper:

* `FiniteChains.RACG.len_mul_of_no_common_desc` — if two elements have no common left descent,
  the lengths of their "difference" add up;
* `FiniteChains.RACG.exists_median` — any three elements of the group have a median vertex in
  the Cayley graph;
* `FiniteChains.RACG.median_unique` — the median is unique.
-/

namespace FiniteChains
namespace RACG

universe u

variable {V : Type u} [DecidableEq V] (A : CommRel V)

theorem gen_inv (s : V) : (gen A s)⁻¹ = gen A s :=
  inv_eq_of_mul_eq_one_left (gen_mul_gen A s)

/-- Cancelling a common generator on the left. -/
theorem gen_mul_inv_cancel (s : V) (x y : CayGroup A) :
    (gen A s * x)⁻¹ * (gen A s * y) = x⁻¹ * y := by
  rw [mul_inv_rev, gen_inv, mul_assoc, gen_mul_gen_mul]

theorem gen_mul_inv_left (s : V) (m x : CayGroup A) :
    (gen A s * m)⁻¹ * x = m⁻¹ * (gen A s * x) := by
  rw [mul_inv_rev, gen_inv, mul_assoc]

theorem inv_mul_inv_mul (m x y : CayGroup A) : (m⁻¹ * x)⁻¹ * (m⁻¹ * y) = x⁻¹ * y := by
  group

theorem clen_pos_of_desc {x : CayGroup A} {s : V} (h : IsDesc A x s) : 0 < clen A x := by
  have := clen_gen_mul_of_desc A h
  omega

/-- A descent of a prefix is a descent. -/
theorem desc_of_prefix {m x : CayGroup A} {s : V}
    (hpre : clen A x = clen A m + clen A (m⁻¹ * x)) (hs : IsDesc A m s) : IsDesc A x s := by
  have hm : clen A (gen A s * m) + 1 = clen A m := clen_gen_mul_of_desc A hs
  have hfac : gen A s * x = (gen A s * m) * (m⁻¹ * x) := by group
  have hle : clen A (gen A s * x) ≤ clen A (gen A s * m) + clen A (m⁻¹ * x) := by
    rw [hfac]; exact clen_mul_le A _ _
  show clen A (gen A s * x) < clen A x
  omega

/-- If `s` shortens `x` but not its prefix `m`, then it shortens the remaining factor. -/
theorem desc_quot_of_prefix {m x : CayGroup A} {s : V}
    (hpre : clen A x = clen A m + clen A (m⁻¹ * x)) (hx : IsDesc A x s) (hm : ¬ IsDesc A m s) :
    IsDesc A (m⁻¹ * x) s := by
  induction hn : clen A m using Nat.strong_induction_on generalizing m x with
  | _ n ih =>
      subst hn
      rcases Nat.eq_zero_or_pos (clen A m) with h0 | h0
      · have hm1 : m = 1 := (clen_eq_zero_iff A).1 h0
        subst hm1
        simpa using hx
      · have hmne : m ≠ 1 := by rintro rfl; rw [clen_one] at h0; omega
        obtain ⟨r, hr⟩ := exists_desc A hmne
        have hrx : IsDesc A x r := desc_of_prefix A hpre hr
        have hrs : r ≠ s := by rintro rfl; exact hm hr
        obtain ⟨hrel, hsx⟩ := desc_two A hrs hrx hx
        set m₁ := gen A r * m with hm₁
        set x₁ := gen A r * x with hx₁
        have hmlen : clen A m₁ + 1 = clen A m := clen_gen_mul_of_desc A hr
        have hxlen : clen A x₁ + 1 = clen A x := clen_gen_mul_of_desc A hrx
        have hquot : m₁⁻¹ * x₁ = m⁻¹ * x := by
          rw [hm₁, hx₁, gen_mul_inv_cancel]
        have hpre₁ : clen A x₁ = clen A m₁ + clen A (m₁⁻¹ * x₁) := by
          rw [hquot]; omega
        have hm₁s : ¬ IsDesc A m₁ s := by
          intro hcon
          have := desc_gen_mul_of_rel A (A.rel_symm hrel) hcon
          rw [hm₁, ← mul_assoc, gen_mul_gen, one_mul] at this
          exact hm this
        have := ih (clen A m₁) (by omega) hpre₁ hsx hm₁s rfl
        rwa [hquot] at this

/-- **No common descent means no cancellation.** -/
theorem len_mul_of_no_common_desc {x y : CayGroup A}
    (h : ∀ s : V, IsDesc A x s → ¬ IsDesc A y s) :
    clen A (x⁻¹ * y) = clen A x + clen A y := by
  induction hn : clen A x using Nat.strong_induction_on generalizing x y with
  | _ n ih =>
      subst hn
      rcases Nat.eq_zero_or_pos (clen A x) with h0 | h0
      · have hx1 : x = 1 := (clen_eq_zero_iff A).1 h0
        subst hx1
        simp [h0]
      · have hxne : x ≠ 1 := by rintro rfl; rw [clen_one] at h0; omega
        obtain ⟨s, hs⟩ := exists_desc A hxne
        have hys : ¬ IsDesc A y s := h s hs
        set x' := gen A s * x with hx'
        set y' := gen A s * y with hy'
        have hxlen : clen A x' + 1 = clen A x := clen_gen_mul_of_desc A hs
        have hylen : clen A y' = clen A y + 1 := clen_gen_mul_of_not_desc A hys
        have hsy' : IsDesc A y' s := desc_gen_mul_of_not_desc A hys
        have hsx' : ¬ IsDesc A x' s := not_desc_gen_mul A hs
        have hno : ∀ r : V, IsDesc A x' r → ¬ IsDesc A y' r := by
          intro r hrx' hry'
          have hrs : s ≠ r := by rintro rfl; exact hsx' hrx'
          obtain ⟨hrel, hry⟩ := desc_two A hrs hsy' hry'
          rw [hy', ← mul_assoc, gen_mul_gen, one_mul] at hry
          have hrx : IsDesc A x r := by
            have := desc_gen_mul_of_rel A (A.rel_symm hrel) hrx'
            rwa [hx', ← mul_assoc, gen_mul_gen, one_mul] at this
          exact h r hrx hry
        have hkey : clen A (x'⁻¹ * y') = clen A x' + clen A y' :=
          ih (clen A x') (by omega) hno rfl
        have hsame : x'⁻¹ * y' = x⁻¹ * y := by
          rw [hx', hy', gen_mul_inv_cancel]
        rw [hsame] at hkey
        omega

/-- The three conditions saying that `m` is a median of `1`, `x` and `y`. -/
def IsMeet (x y m : CayGroup A) : Prop :=
  clen A x = clen A m + clen A (m⁻¹ * x) ∧ clen A y = clen A m + clen A (m⁻¹ * y) ∧
    clen A (x⁻¹ * y) = clen A (m⁻¹ * x) + clen A (m⁻¹ * y)

theorem exists_meet (x y : CayGroup A) : ∃ m, IsMeet A x y m := by
  induction hn : clen A x + clen A y using Nat.strong_induction_on generalizing x y with
  | _ n ih =>
      subst hn
      by_cases hcom : ∃ s : V, IsDesc A x s ∧ IsDesc A y s
      · obtain ⟨s, hsx, hsy⟩ := hcom
        set x' := gen A s * x with hx'
        set y' := gen A s * y with hy'
        have hxlen : clen A x' + 1 = clen A x := clen_gen_mul_of_desc A hsx
        have hylen : clen A y' + 1 = clen A y := clen_gen_mul_of_desc A hsy
        obtain ⟨m', hm'⟩ := ih (clen A x' + clen A y') (by omega) x' y' rfl
        have hsx' : ¬ IsDesc A x' s := not_desc_gen_mul A hsx
        have hm's : ¬ IsDesc A m' s := fun hcon => hsx' (desc_of_prefix A hm'.1 hcon)
        refine ⟨gen A s * m', ?_, ?_, ?_⟩
        · have hmlen : clen A (gen A s * m') = clen A m' + 1 :=
            clen_gen_mul_of_not_desc A hm's
          have hq : (gen A s * m')⁻¹ * x = m'⁻¹ * x' := by
            rw [hx', gen_mul_inv_left]
          rw [hmlen, hq]
          have := hm'.1
          omega
        · have hmlen : clen A (gen A s * m') = clen A m' + 1 :=
            clen_gen_mul_of_not_desc A hm's
          have hq : (gen A s * m')⁻¹ * y = m'⁻¹ * y' := by
            rw [hy', gen_mul_inv_left]
          rw [hmlen, hq]
          have := hm'.2.1
          omega
        · have hq1 : (gen A s * m')⁻¹ * x = m'⁻¹ * x' := by
            rw [hx', gen_mul_inv_left]
          have hq2 : (gen A s * m')⁻¹ * y = m'⁻¹ * y' := by
            rw [hy', gen_mul_inv_left]
          have hq3 : x⁻¹ * y = x'⁻¹ * y' := by
            rw [hx', hy']
            exact (gen_mul_inv_cancel A s x y).symm
          rw [hq1, hq2, hq3]
          exact hm'.2.2
      · refine ⟨1, by simp [clen_one], by simp [clen_one], ?_⟩
        push_neg at hcom
        simp only [inv_one, one_mul]
        exact len_mul_of_no_common_desc A hcom

/-- A common descent of `x` and `y` is a descent of any meet. -/
theorem desc_of_meet {x y m : CayGroup A} {s : V} (hm : IsMeet A x y m)
    (hx : IsDesc A x s) (hy : IsDesc A y s) : IsDesc A m s := by
  by_contra hcon
  have hcx : IsDesc A (m⁻¹ * x) s := desc_quot_of_prefix A hm.1 hx hcon
  have hcy : IsDesc A (m⁻¹ * y) s := desc_quot_of_prefix A hm.2.1 hy hcon
  have h1 : clen A (gen A s * (m⁻¹ * x)) + 1 = clen A (m⁻¹ * x) := clen_gen_mul_of_desc A hcx
  have h2 : clen A (gen A s * (m⁻¹ * y)) + 1 = clen A (m⁻¹ * y) := clen_gen_mul_of_desc A hcy
  have hprod : (gen A s * (m⁻¹ * x))⁻¹ * (gen A s * (m⁻¹ * y)) = x⁻¹ * y := by
    rw [gen_mul_inv_cancel, inv_mul_inv_mul]
  have hle : clen A (x⁻¹ * y)
      ≤ clen A (gen A s * (m⁻¹ * x)) + clen A (gen A s * (m⁻¹ * y)) := by
    rw [← hprod]
    calc clen A ((gen A s * (m⁻¹ * x))⁻¹ * (gen A s * (m⁻¹ * y)))
        ≤ clen A ((gen A s * (m⁻¹ * x))⁻¹) + clen A (gen A s * (m⁻¹ * y)) := clen_mul_le A _ _
      _ = clen A (gen A s * (m⁻¹ * x)) + clen A (gen A s * (m⁻¹ * y)) := by
          rw [clen_inv]
  have h3 := hm.2.2
  omega

theorem meet_unique {x y m m' : CayGroup A} (h : IsMeet A x y m) (h' : IsMeet A x y m') :
    m = m' := by
  induction hn : clen A m using Nat.strong_induction_on generalizing x y m m' with
  | _ n ih =>
      subst hn
      have hlen : clen A m = clen A m' := by
        have e1 := h.1; have e2 := h.2.1; have e3 := h.2.2
        have f1 := h'.1; have f2 := h'.2.1; have f3 := h'.2.2
        omega
      rcases Nat.eq_zero_or_pos (clen A m) with h0 | h0
      · have hm1 : m = 1 := (clen_eq_zero_iff A).1 h0
        have hm'1 : m' = 1 := (clen_eq_zero_iff A).1 (by omega)
        rw [hm1, hm'1]
      · have hmne : m ≠ 1 := by rintro rfl; rw [clen_one] at h0; omega
        obtain ⟨s, hs⟩ := exists_desc A hmne
        have hsx : IsDesc A x s := desc_of_prefix A h.1 hs
        have hsy : IsDesc A y s := desc_of_prefix A h.2.1 hs
        have hs' : IsDesc A m' s := desc_of_meet A h' hsx hsy
        set x₁ := gen A s * x with hx₁
        set y₁ := gen A s * y with hy₁
        have hxlen : clen A x₁ + 1 = clen A x := clen_gen_mul_of_desc A hsx
        have hylen : clen A y₁ + 1 = clen A y := clen_gen_mul_of_desc A hsy
        have hxy : x₁⁻¹ * y₁ = x⁻¹ * y := by
          rw [hx₁, hy₁, gen_mul_inv_cancel]
        have key : ∀ z : CayGroup A, IsMeet A x y z → IsDesc A z s →
            IsMeet A x₁ y₁ (gen A s * z) := by
          intro z hz hzs
          have hzlen : clen A (gen A s * z) + 1 = clen A z := clen_gen_mul_of_desc A hzs
          have hq1 : (gen A s * z)⁻¹ * x₁ = z⁻¹ * x := by
            rw [hx₁, gen_mul_inv_cancel]
          have hq2 : (gen A s * z)⁻¹ * y₁ = z⁻¹ * y := by
            rw [hy₁, gen_mul_inv_cancel]
          refine ⟨?_, ?_, ?_⟩
          · rw [hq1]
            have := hz.1
            omega
          · rw [hq2]
            have := hz.2.1
            omega
          · rw [hq1, hq2, hxy]
            exact hz.2.2
        have h1 := key m h hs
        have h2 := key m' h' hs'
        have hmlen : clen A (gen A s * m) + 1 = clen A m := clen_gen_mul_of_desc A hs
        have := ih (clen A (gen A s * m)) (by omega) h1 h2 rfl
        have hcancel : gen A s * (gen A s * m) = gen A s * (gen A s * m') := by rw [this]
        rwa [gen_mul_gen_mul, gen_mul_gen_mul] at hcancel

/-- `z` is a median of `a`, `b`, `c` in the Cayley graph. -/
def IsMedian (a b c z : CayGroup A) : Prop :=
  cdist A a z + cdist A z b = cdist A a b ∧ cdist A b z + cdist A z c = cdist A b c ∧
    cdist A a z + cdist A z c = cdist A a c

/-- Being a median of `a, b, c` is the same as being a meet after translating `a` to `1`. -/
theorem isMedian_iff_isMeet (a b c z : CayGroup A) :
    IsMedian A a b c z ↔ IsMeet A (a⁻¹ * b) (a⁻¹ * c) (a⁻¹ * z) := by
  have e1 : a⁻¹ * z = a⁻¹ * z := rfl
  have e2 : (a⁻¹ * z)⁻¹ * (a⁻¹ * b) = z⁻¹ * b := by group
  have e3 : (a⁻¹ * z)⁻¹ * (a⁻¹ * c) = z⁻¹ * c := by group
  have e4 : (a⁻¹ * b)⁻¹ * (a⁻¹ * c) = b⁻¹ * c := by group
  have e5 : clen A (b⁻¹ * z) = clen A (z⁻¹ * b) := by
    rw [← clen_inv A (b⁻¹ * z), mul_inv_rev, inv_inv]
  simp only [IsMedian, IsMeet, cdist, e2, e3, e4, e5]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1.symm, h3.symm, h2.symm⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1.symm, h3.symm, h2.symm⟩

theorem exists_median (a b c : CayGroup A) : ∃ z, IsMedian A a b c z := by
  obtain ⟨m, hm⟩ := exists_meet A (a⁻¹ * b) (a⁻¹ * c)
  refine ⟨a * m, ?_⟩
  rw [isMedian_iff_isMeet]
  simpa using hm

theorem median_unique {a b c z z' : CayGroup A} (h : IsMedian A a b c z)
    (h' : IsMedian A a b c z') : z = z' := by
  rw [isMedian_iff_isMeet] at h h'
  have := meet_unique A h h'
  simpa using this

end RACG
end FiniteChains
