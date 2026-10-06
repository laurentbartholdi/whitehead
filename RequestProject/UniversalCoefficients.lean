module

public import Mathlib
public import RequestProject.FoxCommutator

@[expose] public section

/-!
# The universal-coefficient input of Section 2

At the end of Section 2 the paper says: "The universal coefficient theorem gives
`H₂(K_N;ℤ) = 0` and torsion-free `N/[N,N]`", and earlier, in the derivation of (2.3), that
"Fox cycles modulo `p` lift integrally when the universal cover has `H₁ = 0`"
(the reference to Hatcher).

Both assertions are consequences of one purely algebraic fact about the cellular chain
complex of the cover, which is the complex of free `ℤ[G/N]`-modules whose second boundary
is the Fox boundary `∂_{2,N}`.  The requirements (2.2) are imposed integrally *and modulo
every prime*; modulo `p` the requirement says exactly that the boundary is injective after
reduction mod `p`, which in the free (hence torsion-free) setting is the lifting property
`LiftsMod` below.  Given the requirement for every prime, the homology

  `H₁ = (cycles) / im ∂`

is torsion free, and `H₂ = ker ∂ = 0` is immediate from the integral requirement.

This file proves that algebraic statement in general (`mem_range_of_nsmul_mem_range`,
`isAddTorsionFree_quotient_range_of_liftsMod`) and specializes it to the Fox boundary
(`foxHomologyOne_torsionFree`).  Together with the dictionary `H₁(K_N) = N/[N,N]` — the one
topological input that is not formalized here — this is the hypothesis
`IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆))` used in
`RequestProject/FoxCommutator.lean`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open Function

variable {U V : Type*} [AddCommGroup U] [AddCommGroup V]

/-- Multiplication by `n` on an additive commutative group, as a homomorphism. -/
def nsmulHom (n : ℕ) (U : Type*) [AddCommGroup U] : U →+ U where
  toFun u := n • u
  map_zero' := smul_zero n
  map_add' a b := smul_add n a b

@[simp] theorem nsmulHom_apply (n : ℕ) (u : U) : nsmulHom n U u = n • u := rfl

/-- `f` is *injective modulo `n`*: whenever `f u` is divisible by `n`, already `u` is.
For maps between free modules this is injectivity of the reduction `f ⊗ ℤ/n`. -/
def LiftsMod (f : U →+ V) (n : ℕ) : Prop :=
  ∀ u : U, (∃ w : V, f u = n • w) → ∃ u' : U, u = n • u'

theorem nsmulRange_le_comap (f : U →+ V) (n : ℕ) :
    (nsmulHom n U).range ≤ AddSubgroup.comap f (nsmulHom n V).range := by
  rintro u ⟨u', rfl⟩
  exact ⟨f u', by simp [nsmulHom, map_nsmul]⟩

/-- The reduction of `f` modulo `n`, as a map `U/nU → V/nV`. -/
def modHom (f : U →+ V) (n : ℕ) :
    (U ⧸ (nsmulHom n U).range) →+ (V ⧸ (nsmulHom n V).range) :=
  QuotientAddGroup.map _ _ f (nsmulRange_le_comap f n)

/-- `LiftsMod f n` is precisely injectivity of the induced map `U/nU → V/nV`, i.e. of the
reduction of `f` modulo `n`. -/
theorem liftsMod_iff_injective_modHom (f : U →+ V) (n : ℕ) :
    LiftsMod f n ↔ Injective (modHom f n) := by
  constructor
  · intro h
    rw [injective_iff_map_eq_zero]
    intro q hq
    induction q using QuotientAddGroup.induction_on with
    | H u =>
      rw [modHom, QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff] at hq
      obtain ⟨w, hw⟩ := hq
      obtain ⟨u', hu'⟩ := h u ⟨w, by simpa [nsmulHom] using hw.symm⟩
      rw [QuotientAddGroup.eq_zero_iff]
      exact ⟨u', by simp [nsmulHom, hu']⟩
  · intro h u ⟨w, hw⟩
    have hq : modHom f n (QuotientAddGroup.mk u) = 0 := by
      rw [modHom, QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff]
      exact ⟨w, by simpa [nsmulHom] using hw.symm⟩
    have := (injective_iff_map_eq_zero (modHom f n)).1 h _ hq
    rw [QuotientAddGroup.eq_zero_iff] at this
    obtain ⟨u', hu'⟩ := this
    exact ⟨u', by simpa [nsmulHom, eq_comm] using hu'⟩

/-- **The lifting step.**  If the target is torsion free and `f` is injective modulo every
prime, then every element whose multiple lies in the image already lies in the image. -/
theorem mem_range_of_nsmul_mem_range (f : U →+ V) [IsAddTorsionFree V]
    (hmod : ∀ p : ℕ, p.Prime → LiftsMod f p) :
    ∀ n : ℕ, n ≠ 0 → ∀ x : V, n • x ∈ f.range → x ∈ f.range := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn x hx
    rcases eq_or_ne n 1 with rfl | hn1
    · simpa using hx
    · obtain ⟨p, hp, m, rfl⟩ : ∃ p, p.Prime ∧ ∃ m, n = p * m := by
        obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hn1
        obtain ⟨m, rfl⟩ := hdvd
        exact ⟨p, hp, m, rfl⟩
      have hm : m ≠ 0 := by rintro rfl; simp at hn
      have hpos : p ≠ 0 := hp.ne_zero
      obtain ⟨u, hu⟩ := hx
      -- `p` divides `f u`, hence `u`
      obtain ⟨u', hu'⟩ := hmod p hp u ⟨m • x, by rw [hu, mul_smul]⟩
      have hmx : m • x = f u' := by
        refine IsAddTorsionFree.nsmul_right_injective hpos ?_
        show p • (m • x) = p • f u'
        rw [← mul_smul, ← hu, hu', map_nsmul]
      have : m • x ∈ f.range := ⟨u', hmx.symm⟩
      rcases eq_or_ne m 1 with rfl | hm1
      · simpa using this
      · refine ih m ?_ hm x this
        have h2 := hp.two_le
        have hm' := Nat.pos_of_ne_zero hm
        nlinarith

/-- **Torsion freeness of the cokernel.**  If the target is torsion free and `f` is
injective modulo every prime, then `V / im f` is torsion free. -/
theorem isAddTorsionFree_quotient_range_of_liftsMod (f : U →+ V) [IsAddTorsionFree V]
    (hmod : ∀ p : ℕ, p.Prime → LiftsMod f p) :
    IsAddTorsionFree (V ⧸ f.range) := by
  constructor
  intro n hn a b hab
  induction a using QuotientAddGroup.induction_on with
  | H x =>
    induction b using QuotientAddGroup.induction_on with
    | H y =>
      have hmk : ((n • x : V) : V ⧸ f.range) = ((n • y : V) : V ⧸ f.range) := by
        simpa [QuotientAddGroup.mk_nsmul] using hab
      have h0 : (n • (x - y) : V) ∈ f.range := by
        refine (QuotientAddGroup.eq_zero_iff _).1 ?_
        rw [smul_sub, QuotientAddGroup.mk_sub, hmk, sub_self]
      have hmem := mem_range_of_nsmul_mem_range f hmod n hn _ h0
      have hzero : ((x - y : V) : V ⧸ f.range) = 0 := (QuotientAddGroup.eq_zero_iff _).2 hmem
      rw [QuotientAddGroup.mk_sub, sub_eq_zero] at hzero
      exact hzero

/-- Torsion freeness passes to subgroups; applied to the homology `H₁ = Z / im ∂`, a
subgroup of the cokernel `V / im ∂`. -/
theorem isAddTorsionFree_subgroup {A : Type*} [AddGroup A] [IsAddTorsionFree A]
    (B : AddSubgroup A) : IsAddTorsionFree B := by
  constructor
  intro n hn a b hab
  have : (n • (a : A)) = n • (b : A) := congrArg Subtype.val hab
  exact Subtype.ext (IsAddTorsionFree.nsmul_right_injective hn this)

/-!
## The Fox complex
-/

/-- Finitely supported functions into a torsion-free group are torsion free. -/
instance isAddTorsionFree_finsupp {α : Type*} {A : Type*} [AddCommGroup A]
    [IsAddTorsionFree A] : IsAddTorsionFree (α →₀ A) := by
  constructor
  intro n hn a b hab
  refine Finsupp.ext fun i => ?_
  have : (n • a) i = (n • b) i := congrArg (fun v : α →₀ A => v i) hab
  simpa using IsAddTorsionFree.nsmul_right_injective hn (by simpa using this)

/-- Group rings over `ℤ` are torsion free as additive groups. -/
instance isAddTorsionFree_monoidAlgebra {Q : Type*} [Monoid Q] :
    IsAddTorsionFree (MonoidAlgebra ℤ Q) :=
  by
    constructor
    intro n hn a b hab
    let e := (MonoidAlgebra.coeffAddEquiv (R := ℤ) (M := Q)).toAddMonoidHom
    have hc : n • a.coeff = n • b.coeff := calc
      _ = e (n • a) := (map_nsmul e n a).symm
      _ = e (n • b) := congrArg e hab
      _ = _ := map_nsmul e n b
    apply MonoidAlgebra.coeff_injective
    exact IsAddTorsionFree.nsmul_right_injective hn hc

variable {G : Type*} [Group G] {I J : Type*}

/-- The cokernel of the reduced Fox boundary; the first homology `H₁(K_N)` of the cover is
a subgroup of it. -/
abbrev foxCokernel (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (N : Subgroup G) [N.Normal] : Type _ :=
  (I →₀ MonoidAlgebra ℤ (G ⧸ N)) ⧸ (boundaryMap b hcol N).toAddMonoidHom.range

/-- **`H₂(K_N) = ker ∂_{2,N} = 0`.**  The integral requirement (2.2) says precisely that
the reduced Fox boundary is injective, so the second homology of the cover vanishes. -/
theorem foxHomologyTwo_eq_bot (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (N : Subgroup G) [N.Normal]
    (h : ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v N) :
    LinearMap.ker (boundaryMap b hcol N) = ⊥ :=
  LinearMap.ker_eq_bot'.2 fun u hu =>
    (forall_foxSat_iff_injective b hcol N).1 h (by rw [hu, map_zero])

/-- **Torsion freeness of `H₁` of the cover.**  If the reduced Fox boundary is injective
modulo every prime — the requirements (2.2) modulo `p`, for all `p` — then the cokernel of
the boundary, and hence its subgroup `H₁(K_N) = (cycles)/im ∂_{2,N}`, is torsion free.

Through the dictionary `H₁(K_N) = N/[N,N]` this is the input that Section 2 quotes from the
universal coefficient theorem before applying Lemma 2.1. -/
theorem foxCokernel_torsionFree (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (N : Subgroup G) [N.Normal]
    (hmod : ∀ p : ℕ, p.Prime →
      LiftsMod (boundaryMap b hcol N).toAddMonoidHom p) :
    IsAddTorsionFree (foxCokernel b hcol N) :=
  isAddTorsionFree_quotient_range_of_liftsMod _ hmod

/-- The same statement for the homology itself: any subgroup of cycles modulo the image of
the boundary — in particular `H₁(K_N)` — is torsion free. -/
theorem foxHomologyOne_torsionFree (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (N : Subgroup G) [N.Normal]
    (hmod : ∀ p : ℕ, p.Prime → LiftsMod (boundaryMap b hcol N).toAddMonoidHom p)
    (Z : AddSubgroup (foxCokernel b hcol N)) :
    IsAddTorsionFree Z := by
  haveI := foxCokernel_torsionFree b hcol N hmod
  exact isAddTorsionFree_subgroup Z

/-!
## Removing the torsion-freeness hypothesis from the application of Lemma 2.1
-/

/-- A group written multiplicatively out of a torsion-free additive group is torsion free. -/
instance isMulTorsionFree_multiplicative {A : Type*} [AddMonoid A] [IsAddTorsionFree A] :
    IsMulTorsionFree (Multiplicative A) := by
  constructor
  intro n hn a b hab
  have h : n • (Multiplicative.toAdd a) = n • (Multiplicative.toAdd b) := hab
  exact IsAddTorsionFree.nsmul_right_injective (M := A) hn h

/-- Torsion freeness transfers along an injective homomorphism. -/
theorem isMulTorsionFree_of_injective {M A : Type*} [Monoid M] [Monoid A] [IsMulTorsionFree A]
    (f : M →* A) (hf : ∀ a b : M, f a = f b → a = b) : IsMulTorsionFree M := by
  constructor
  intro n hn a b hab
  exact hf a b (IsMulTorsionFree.pow_left_injective hn
    (by simpa only [← map_pow] using congrArg f hab))

/-- **The requirements pass to the commutator subgroup, with the universal-coefficient input
now proved.**  Assume the requirements (2.2) for `N` integrally and, in the lifting form
`LiftsMod`, modulo every prime.  Then the only remaining input for the conclusion of
Section 2 is the topological dictionary `H₁(K_N) = N/[N,N]`, here in the weakest form that
is needed: an injective homomorphism from `N/[N,N]` into the cokernel of the Fox boundary
(the first homology of the cover sits inside that cokernel).  Torsion freeness of `N/[N,N]`
is then a theorem rather than a hypothesis, and the requirements pass to `[N, N]`. -/
theorem foxSat_commutator_of_hurewicz (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (N : Subgroup G) [N.Normal]
    (hmod : ∀ p : ℕ, p.Prime → LiftsMod (boundaryMap b hcol N).toAddMonoidHom p)
    (dict : (N.map (QuotientGroup.mk' ⁅N, N⁆)) →* Multiplicative (foxCokernel b hcol N))
    (hdict : ∀ a b, dict a = dict b → a = b)
    (h : ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v N) :
    ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v ⁅N, N⁆ := by
  haveI : IsAddTorsionFree (foxCokernel b hcol N) := foxCokernel_torsionFree b hcol N hmod
  haveI : IsMulTorsionFree (Multiplicative (foxCokernel b hcol N)) :=
    isMulTorsionFree_multiplicative
  haveI : IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆)) := by
    constructor
    intro n hn a c hab
    have hpow : dict a ^ n = dict c ^ n := by
      simpa only [← map_pow] using congrArg dict hab
    exact hdict a c (IsMulTorsionFree.pow_left_injective
      (M := Multiplicative (foxCokernel b hcol N)) hn hpow)
  exact foxSat_commutator b hcol N h

end FiniteChains
