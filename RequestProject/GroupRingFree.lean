module

public import Mathlib

@[expose] public section

/-!
# `k[Q]` is a free `k[H]`-module on coset representatives

Lemma 2.1 of the paper is reduced, in its "outline of a direct proof", to a
statement about free modules over the commutative domain `k[H]` by means of the
remark that

> the free modules remain free, since `k[Q]` is free over `k[H]` on coset
> representatives.

This file proves exactly that remark, with no hypotheses on `k`, `Q` or `H`
beyond `k` a commutative ring, `Q` a group and `H ≤ Q` a subgroup: the group
algebra `k[Q]`, viewed as a left module over `k[H]` through the inclusion
`k[H] → k[Q]`, is free with basis the right cosets `H \ Q`, a basis element
being the chosen representative of the coset.

The commutative-algebra core of Lemma 2.1 itself is in
`RequestProject/QuotientInjectivity.lean`.
-/

namespace FiniteChains

open MonoidAlgebra

variable (k : Type*) [CommRing k] {Q : Type*} [Group Q] (H : Subgroup Q)

/-- The right cosets `H \ Q`; left multiplication by `H` preserves a class. -/
abbrev RightCosets : Type _ := Quotient (QuotientGroup.rightRel H)

/-- The inclusion of group algebras `k[H] → k[Q]`. -/
noncomputable def groupRingIncl : MonoidAlgebra k H →+* MonoidAlgebra k Q :=
  MonoidAlgebra.mapDomainRingHom k H.subtype

/-- `k[Q]` as a left module over `k[H]`. -/
noncomputable instance moduleGroupRing :
    Module (MonoidAlgebra k H) (MonoidAlgebra k Q) := (groupRingIncl k H).toModule

variable {k H}

theorem groupRingIncl_apply_mem (x : MonoidAlgebra k H) (q : Q) (hq : q ∈ H) :
    (groupRingIncl k H x).coeff q = x.coeff (⟨q, hq⟩ : H) :=
  Finsupp.mapDomain_apply_of_injective Subtype.val_injective x.coeff (⟨q, hq⟩ : H)

theorem groupRingIncl_apply_notMem (x : MonoidAlgebra k H) (q : Q) (hq : q ∉ H) :
    (groupRingIncl k H x).coeff q = 0 := by
  refine Finsupp.mapDomain_notin_range x.coeff q ?_
  rintro ⟨⟨h, hh⟩, rfl⟩
  exact hq hh

theorem smul_def' (x : MonoidAlgebra k H) (y : MonoidAlgebra k Q) :
    x • y = groupRingIncl k H x * y := rfl

theorem groupRingIncl_single (h : H) (a : k) :
    groupRingIncl k H (single h a) = single (h : Q) a :=
  MonoidAlgebra.mapDomain_single

variable (k H)

/-- The chosen representative of a right coset. -/
noncomputable def cosetRep (c : RightCosets H) : Q := c.out

variable {k H}

theorem mul_cosetRep_inv_mem (q : Q) :
    q * (cosetRep H (Quotient.mk (QuotientGroup.rightRel H) q))⁻¹ ∈ H := by
  have h : (Quotient.mk (QuotientGroup.rightRel H) q) =
      Quotient.mk (QuotientGroup.rightRel H)
        (cosetRep H (Quotient.mk (QuotientGroup.rightRel H) q)) :=
    (Quotient.out_eq _).symm
  have := Quotient.exact h.symm
  exact QuotientGroup.rightRel_apply.mp this

theorem mk_eq_iff {q r : Q} :
    Quotient.mk (QuotientGroup.rightRel H) q = Quotient.mk (QuotientGroup.rightRel H) r ↔
      r * q⁻¹ ∈ H := by
  rw [Quotient.eq]
  exact QuotientGroup.rightRel_apply

/-- The `k[H]`-linear map `(H \ Q →₀ k[H]) → k[Q]` sending the `c`-th basis vector to the
chosen representative of the coset `c`. -/
noncomputable def cosetCombination :
    (RightCosets H →₀ MonoidAlgebra k H) →ₗ[MonoidAlgebra k H] MonoidAlgebra k Q :=
  Finsupp.linearCombination (MonoidAlgebra k H) fun c => single (cosetRep H c) (1 : k)

/-- The coefficients of `cosetCombination`: the `q`-th coefficient only sees the coset of
`q`, at the position `q · (rep of its coset)⁻¹` of `H`. -/
theorem cosetCombination_apply (F : RightCosets H →₀ MonoidAlgebra k H) (q : Q) :
    (cosetCombination F).coeff q =
      (F (Quotient.mk (QuotientGroup.rightRel H) q)).coeff
        ⟨q * (cosetRep H (Quotient.mk (QuotientGroup.rightRel H) q))⁻¹,
          mul_cosetRep_inv_mem q⟩ := by
  classical
  rw [cosetCombination, Finsupp.linearCombination_apply, Finsupp.sum]
  have hterm : ∀ c ∈ F.support,
      (F c • single (cosetRep H c) (1 : k) : MonoidAlgebra k Q).coeff q =
        if Quotient.mk (QuotientGroup.rightRel H) q = c then
          (F (Quotient.mk (QuotientGroup.rightRel H) q)).coeff
            ⟨q * (cosetRep H (Quotient.mk (QuotientGroup.rightRel H) q))⁻¹,
              mul_cosetRep_inv_mem q⟩
        else 0 := by
    intro c _
    rw [smul_def', MonoidAlgebra.coeff_mul_single_apply, mul_one]
    by_cases hc : Quotient.mk (QuotientGroup.rightRel H) q = c
    · subst hc
      rw [if_pos rfl]
      exact groupRingIncl_apply_mem _ _ (mul_cosetRep_inv_mem q)
    · rw [if_neg hc]
      refine groupRingIncl_apply_notMem _ _ ?_
      intro hmem
      apply hc
      have : Quotient.mk (QuotientGroup.rightRel H) q =
          Quotient.mk (QuotientGroup.rightRel H) (cosetRep H c) := by
        rw [mk_eq_iff]
        simpa using (Subgroup.inv_mem _ hmem)
      rw [this]
      exact Quotient.out_eq c
  have hsum : (∑ c ∈ F.support, F c • single (cosetRep H c) (1 : k) : MonoidAlgebra k Q).coeff q
      = ∑ c ∈ F.support, (F c • single (cosetRep H c) (1 : k) : MonoidAlgebra k Q).coeff q := by
    simp [MonoidAlgebra.coeff_sum]
  rw [hsum, Finset.sum_congr rfl hterm, Finset.sum_ite_eq F.support]
  by_cases hq : Quotient.mk (QuotientGroup.rightRel H) q ∈ F.support
  · rw [if_pos hq]
  · rw [if_neg hq]
    have : F (Quotient.mk (QuotientGroup.rightRel H) q) = 0 := by
      simpa using hq
    simp [this]

/-- The inverse bijection `Q ≃ (H \ Q) × H`. -/
noncomputable def cosetEquiv : Q ≃ (RightCosets H × H) where
  toFun q := (Quotient.mk (QuotientGroup.rightRel H) q,
    ⟨q * (cosetRep H (Quotient.mk (QuotientGroup.rightRel H) q))⁻¹, mul_cosetRep_inv_mem q⟩)
  invFun p := (p.2 : Q) * cosetRep H p.1
  left_inv q := by simp
  right_inv p := by
    obtain ⟨c, h, hh⟩ := p
    have hmk : Quotient.mk (QuotientGroup.rightRel H) ((h : Q) * cosetRep H c) = c := by
      have : Quotient.mk (QuotientGroup.rightRel H) ((h : Q) * cosetRep H c) =
          Quotient.mk (QuotientGroup.rightRel H) (cosetRep H c) := by
        rw [mk_eq_iff]
        simpa using Subgroup.inv_mem _ hh
      rw [this]; exact Quotient.out_eq c
    ext
    · exact hmk
    · simp [hmk]

/-- `cosetCombination` is bijective: `k[Q]` is free over `k[H]` on coset representatives. -/
theorem cosetCombination_bijective :
    Function.Bijective (cosetCombination (k := k) (H := H)) := by
  classical
  constructor
  · intro F G hFG
    ext c h
    have h1 := congrArg (fun f : MonoidAlgebra k Q => f.coeff ((h : Q) * cosetRep H c)) hFG
    simp only [cosetCombination_apply] at h1
    have hmk : Quotient.mk (QuotientGroup.rightRel H) ((h : Q) * cosetRep H c) = c :=
      congrArg Prod.fst ((cosetEquiv (H := H)).right_inv (c, h))
    simp only [hmk] at h1
    have heq : (⟨(h : Q) * cosetRep H c * (cosetRep H c)⁻¹,
        show (h : Q) * cosetRep H c * (cosetRep H c)⁻¹ ∈ H by
          simpa [hmk] using mul_cosetRep_inv_mem ((h : Q) * cosetRep H c)⟩ : H) = h := by
      ext; simp
    simp only [heq] at h1
    exact h1
  · intro f
    refine MonoidAlgebra.induction f ⟨0, map_zero _⟩ ?_
    rintro q a g - - ⟨G, hG⟩
    refine ⟨Finsupp.single (Quotient.mk (QuotientGroup.rightRel H) q)
      (single ⟨q * (cosetRep H (Quotient.mk (QuotientGroup.rightRel H) q))⁻¹,
        mul_cosetRep_inv_mem q⟩ a) + G, ?_⟩
    rw [map_add, hG, cosetCombination, Finsupp.linearCombination_single, smul_def',
      groupRingIncl_single, MonoidAlgebra.single_mul_single]
    simp

/-- The basis of `k[Q]` over `k[H]` given by coset representatives. -/
noncomputable def cosetBasis :
    Module.Basis (RightCosets H) (MonoidAlgebra k H) (MonoidAlgebra k Q) :=
  Module.Basis.ofRepr
    (LinearEquiv.ofBijective (cosetCombination (k := k) (H := H))
      cosetCombination_bijective).symm

/-- The basis vector attached to a coset is its chosen representative. -/
theorem cosetBasis_apply (c : RightCosets H) :
    cosetBasis (k := k) (H := H) c = single (cosetRep H c) (1 : k) := by
  rw [cosetBasis, Module.Basis.coe_ofRepr]
  simp [cosetCombination]

/-- **`k[Q]` is a free `k[H]`-module.** -/
instance groupRing_free : Module.Free (MonoidAlgebra k H) (MonoidAlgebra k Q) :=
  Module.Free.of_basis (cosetBasis (k := k) (H := H))

end FiniteChains
