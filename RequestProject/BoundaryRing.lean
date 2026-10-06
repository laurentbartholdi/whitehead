module

public import Mathlib
public import RequestProject.LemmaTwoOne

@[expose] public section

/-!
# The reduced Fox boundary over an arbitrary coefficient ring

Section 2 of the paper imposes the requirements (2.2) on the reduced Fox boundary
`∂_{2,M}` both over `ℤ` and over `𝔽ₚ` for every prime `p`.  This file sets up the reduced
boundary over an arbitrary commutative coefficient ring `k`, together with the application
of Lemma 2.1 that was carried out over `ℤ` in `RequestProject/FoxCommutator.lean`:

> if `C ≤ N` are normal subgroups of `G` with `N/C` torsion-free abelian and `k` is an
> integral domain, then injectivity of `∂_{2,N}` over `k[G/N]` implies injectivity of
> `∂_{2,C}` over `k[G/C]`.

The case `k = ℤ` is the integral half of the argument, the case `k = 𝔽ₚ` the half modulo a
prime.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

variable (k : Type*) [CommRing k] {G : Type*} [Group G] {I J : Type*}

/-- Coefficientwise reduction of a vector over `k[G]` to a vector over `k[G/M]`. -/
noncomputable def redVecK (M : Subgroup G) [M.Normal] (v : J →₀ MonoidAlgebra k G) :
    J →₀ MonoidAlgebra k (G ⧸ M) :=
  Finsupp.mapRange (quotRingHom k M) (map_zero _) v

variable {k}

@[simp] theorem redVecK_apply (M : Subgroup G) [M.Normal] (v : J →₀ MonoidAlgebra k G) (j : J) :
    redVecK k M v j = quotRingHom k M (v j) := rfl

variable (k) in
/-- The `j`-th column of the reduced boundary matrix, over `k`. -/
noncomputable def boundaryColK (b : I → J → MonoidAlgebra k G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal] (j : J) :
    I →₀ MonoidAlgebra k (G ⧸ M) :=
  Finsupp.onFinset (hcol j).toFinset (fun i => quotRingHom k M (b i j)) (by
    intro i hi
    simp only [ne_eq] at hi
    have hb : b i j ≠ 0 := fun h => hi (by rw [h, map_zero])
    simpa using hb)

@[simp] theorem boundaryColK_apply (b : I → J → MonoidAlgebra k G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal] (j : J) (i : I) :
    boundaryColK k b hcol M j i = quotRingHom k M (b i j) := rfl

variable (k) in
/-- The Fox boundary `∂_{2,M}` as a map of free left `k[G/M]`-modules. -/
noncomputable def boundaryMapK (b : I → J → MonoidAlgebra k G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal] :
    (J →₀ MonoidAlgebra k (G ⧸ M)) →ₗ[MonoidAlgebra k (G ⧸ M)]
      (I →₀ MonoidAlgebra k (G ⧸ M)) :=
  Finsupp.linearCombination _ (boundaryColK k b hcol M)

theorem boundaryMapK_apply_coord (b : I → J → MonoidAlgebra k G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal]
    (u : J →₀ MonoidAlgebra k (G ⧸ M)) (i : I) :
    boundaryMapK k b hcol M u i = ∑ j ∈ u.support, u j * quotRingHom k M (b i j) := by
  classical
  rw [boundaryMapK, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finset_sum_apply]
  exact Finset.sum_congr rfl fun j _ => rfl

theorem boundaryMapK_single (b : I → J → MonoidAlgebra k G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal] (j : J) :
    boundaryMapK k b hcol M (Finsupp.single j (1 : MonoidAlgebra k (G ⧸ M)))
      = boundaryColK k b hcol M j := by
  rw [boundaryMapK, Finsupp.linearCombination_single, one_smul]

variable (k) in
/-- The `i`-th coordinate of the Fox boundary of the coefficient vector `v`, over `k`. -/
noncomputable def foxBoundaryK (b : I → J → MonoidAlgebra k G)
    (v : J →₀ MonoidAlgebra k G) (i : I) : MonoidAlgebra k G :=
  ∑ j ∈ v.support, v j * b i j

theorem boundaryMapK_redVecK (b : I → J → MonoidAlgebra k G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal]
    (v : J →₀ MonoidAlgebra k G) (i : I) :
    boundaryMapK k b hcol M (redVecK k M v) i = quotRingHom k M (foxBoundaryK k b v i) := by
  classical
  have hsupp : (redVecK k M v).support ⊆ v.support := by
    intro j hj
    simp only [Finsupp.mem_support_iff, redVecK_apply] at hj ⊢
    intro h
    exact hj (by rw [h, map_zero])
  rw [boundaryMapK_apply_coord, foxBoundaryK, map_sum,
    Finset.sum_congr rfl (fun j (_ : j ∈ v.support) => map_mul (quotRingHom k M) (v j) (b i j))]
  refine Finset.sum_subset hsupp ?_
  intro j _ hj
  simp only [Finsupp.mem_support_iff, not_not, redVecK_apply] at hj
  rw [redVecK_apply, hj, zero_mul]

/-- Reduction of coefficient vectors is surjective. -/
theorem quotRingHomK_surjective (M : Subgroup G) [M.Normal] :
    Function.Surjective (quotRingHom k M) := by
  intro y
  obtain ⟨x, hx⟩ := Finsupp.mapDomain_surjective (M := k) (QuotientGroup.mk'_surjective M) y.coeff
  exact ⟨MonoidAlgebra.ofCoeff x, MonoidAlgebra.coeff_injective hx⟩

/-- Every vector over `k[G/M]` lifts to a vector over `k[G]`. -/
theorem exists_liftK (M : Subgroup G) [M.Normal] (u : J →₀ MonoidAlgebra k (G ⧸ M)) :
    ∃ v : J →₀ MonoidAlgebra k G, redVecK k M v = u := by
  classical
  choose lift hlift using quotRingHomK_surjective (k := k) (G := G) M
  refine ⟨Finsupp.mapRange (fun y => if y = 0 then 0 else lift y) (by simp) u, ?_⟩
  refine Finsupp.ext fun j => ?_
  simp only [redVecK_apply, Finsupp.mapRange_apply]
  by_cases h : u j = 0 <;> simp [h, hlift]

/-- **Lemma 2.1 for a pair of normal subgroups, over an arbitrary domain of
coefficients.**  If `C ≤ N` are normal subgroups of `G` with `N/C` torsion-free abelian,
then injectivity of the boundary reduced modulo `N` implies injectivity of the boundary
reduced modulo `C`. -/
theorem injective_boundaryMapK_of_injective [IsDomain k] (b : I → J → MonoidAlgebra k G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (C N : Subgroup G) [C.Normal] [N.Normal]
    (hCN : C ≤ N)
    [IsMulCommutative (N.map (QuotientGroup.mk' C))]
    [IsMulTorsionFree (N.map (QuotientGroup.mk' C))]
    (h : Function.Injective (boundaryMapK k b hcol N)) :
    Function.Injective (boundaryMapK k b hcol C) := by
  classical
  set H : Subgroup (G ⧸ C) := N.map (QuotientGroup.mk' C) with hH
  set e : ((G ⧸ C) ⧸ H) ≃* (G ⧸ N) := QuotientGroup.quotientQuotientEquivQuotient C N hCN with he
  set E : MonoidAlgebra k ((G ⧸ C) ⧸ H) →+* MonoidAlgebra k (G ⧸ N) :=
    MonoidAlgebra.mapDomainRingHom k e.toMonoidHom with hE
  -- the two reductions of `k[G]` agree
  have L1 : ∀ x : MonoidAlgebra k G,
      E (quotRingHom k H (quotRingHom k C x)) = quotRingHom k N x := by
    intro x
    have key : (E.comp ((quotRingHom k H).comp (quotRingHom k C)) : MonoidAlgebra k G →+* _)
        = quotRingHom k N := by
      apply MonoidAlgebra.ringHom_ext
      · intro r
        simp [hE, quotRingHom, MonoidAlgebra.mapDomainRingHom, Finsupp.mapDomain_single]
      · intro g
        simp [hE, quotRingHom, MonoidAlgebra.mapDomainRingHom, Finsupp.mapDomain_single, he]
        rfl
    exact congrArg (fun f : MonoidAlgebra k G →+* MonoidAlgebra k (G ⧸ N) => f x) key
  have hEinj : Function.Injective E :=
    fun _ _ h => MonoidAlgebra.coeff_injective (Finsupp.mapDomain_injective (M := k) e.injective (congrArg MonoidAlgebra.coeff h))
  have hEv : Function.Injective (Finsupp.mapRange (α := J) E (map_zero _)) :=
    Finsupp.mapRange_injective E (map_zero _) hEinj
  -- the columns correspond
  have hcolumn : ∀ j : J,
      Finsupp.mapRange E (map_zero _)
          (reduceVecQ k H (boundaryMapK k b hcol C (Finsupp.single j 1))) =
        boundaryColK k b hcol N j := by
    intro j
    refine Finsupp.ext fun i => ?_
    rw [Finsupp.mapRange_apply, reduceVecQ_apply, boundaryColK_apply,
      boundaryMapK_single, boundaryColK_apply]
    exact L1 (b i j)
  -- the square: reduction over `k[Q]` corresponds to reduction modulo `N`
  have hsq : ∀ w : J →₀ MonoidAlgebra k ((G ⧸ C) ⧸ H),
      Finsupp.mapRange E (map_zero _) (reduceLinQ k H (boundaryMapK k b hcol C) w) =
        boundaryMapK k b hcol N (Finsupp.mapRange E (map_zero _) w) := by
    intro w
    induction w using Finsupp.induction_linear with
    | zero => simp
    | add w₁ w₂ h₁ h₂ =>
        rw [map_add, Finsupp.mapRange_add (by simp) (f := E), h₁, h₂,
          Finsupp.mapRange_add (by simp) (f := E), map_add]
    | single j y =>
        have hsmul : Finsupp.mapRange E (map_zero _)
            (y • reduceVecQ k H (boundaryMapK k b hcol C (Finsupp.single j 1))) =
            E y • Finsupp.mapRange E (map_zero _)
              (reduceVecQ k H (boundaryMapK k b hcol C (Finsupp.single j 1))) := by
          refine Finsupp.ext fun i => ?_
          simp only [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul, map_mul]
        rw [reduceLinQ_single, Finsupp.mapRange_single, hsmul, hcolumn j]
        conv_rhs => rw [boundaryMapK, Finsupp.linearCombination_single]
  -- the reduced map is injective, so Lemma 2.1 applies
  have hred : Function.Injective (reduceLinQ k H (boundaryMapK k b hcol C)) := by
    intro w z hwz
    refine hEv ?_
    have h1 : boundaryMapK k b hcol N (Finsupp.mapRange E (map_zero _) w) =
        boundaryMapK k b hcol N (Finsupp.mapRange E (map_zero _) z) := by
      rw [← hsq w, ← hsq z, hwz]
    exact h h1
  exact injective_of_reduceLinQ_injective (boundaryMapK k b hcol C) hred

end FiniteChains
