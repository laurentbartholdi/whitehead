import Mathlib
import RequestProject.FoxCommutatorMod

/-!
# The requirements pass to the isolator of the commutator subgroup

At the end of Section 2 the paper applies Lemma 2.1 to the pair `[N, N] ≤ N`, which needs
`N/[N, N]` to be torsion free — the input quoted from the universal coefficient theorem.

Lemma 2.1 itself, however, applies to *any* pair `C ≤ N` of normal subgroups with `N/C`
torsion-free abelian, and one such subgroup always exists, with no extra hypothesis: the
isolator

  `C = {x ∈ N : xᵏ ∈ [N, N] for some k ≥ 1}`,

that is, the preimage in `N` of the torsion subgroup of `N/[N, N]`.  This file constructs
it and proves, **unconditionally**, that the requirements (2.2) — integrally and modulo
every prime — pass from `N` to `C`.

Together with the compactness and minimality steps of Section 2 this makes the following
unconditional: a minimal normal subgroup satisfying all the requirements has *torsion*
abelianization.  The universal-coefficient input of the paper is exactly what upgrades
"torsion" to "trivial", that is, to perfectness of `N`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped commutatorElement

namespace FiniteChains

open MonoidAlgebra

variable {G : Type*} [Group G]

/-! ### The isolator of the commutator subgroup -/

/-- The isolator of `[N, N]` in `N`: the elements of `N` some positive power of which lies
in `[N, N]`.  It is the preimage of the torsion subgroup of the abelian group
`N/[N, N]`. -/
def isolatorComm (N : Subgroup G) [N.Normal] : Subgroup G where
  carrier := {x | x ∈ N ∧ ∃ k : ℕ, 0 < k ∧ x ^ k ∈ ⁅N, N⁆}
  one_mem' := ⟨N.one_mem, 1, one_pos, by simp⟩
  mul_mem' := by
    rintro x y ⟨hxN, k, hk, hx⟩ ⟨hyN, l, hl, hy⟩
    refine ⟨N.mul_mem hxN hyN, k * l, Nat.mul_pos hk hl, ?_⟩
    -- in `G/[N, N]` the images of `x` and `y` commute
    have heq : (QuotientGroup.mk' (⁅N, N⁆ : Subgroup G) x) *
        (QuotientGroup.mk' (⁅N, N⁆ : Subgroup G) y)
        = (QuotientGroup.mk' (⁅N, N⁆ : Subgroup G) y) *
          (QuotientGroup.mk' (⁅N, N⁆ : Subgroup G) x) := by
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq]
      have hgr : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by group
      rw [hgr]
      exact Subgroup.commutator_mem_commutator (N.inv_mem hyN) (N.inv_mem hxN)
    have hcomm : Commute (QuotientGroup.mk' (⁅N, N⁆ : Subgroup G) x)
        (QuotientGroup.mk' (⁅N, N⁆ : Subgroup G) y) := heq
    have hxk : (QuotientGroup.mk' (⁅N, N⁆ : Subgroup G) x) ^ k = 1 := by
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hx
    have hyl : (QuotientGroup.mk' (⁅N, N⁆ : Subgroup G) y) ^ l = 1 := by
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hy
    have hmul : (QuotientGroup.mk' (⁅N, N⁆ : Subgroup G)) ((x * y) ^ (k * l)) = 1 := by
      rw [map_pow, map_mul, hcomm.mul_pow, pow_mul, hxk, one_pow, one_mul, mul_comm k l,
        pow_mul, hyl, one_pow]
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmul
  inv_mem' := by
    rintro x ⟨hxN, k, hk, hx⟩
    exact ⟨N.inv_mem hxN, k, hk, by rw [inv_pow]; exact Subgroup.inv_mem _ hx⟩

@[simp] theorem mem_isolatorComm {N : Subgroup G} [N.Normal] {x : G} :
    x ∈ isolatorComm N ↔ x ∈ N ∧ ∃ k : ℕ, 0 < k ∧ x ^ k ∈ ⁅N, N⁆ := by
  simp [isolatorComm, Subgroup.mem_mk, Set.mem_setOf_eq]

theorem isolatorComm_le (N : Subgroup G) [N.Normal] : isolatorComm N ≤ N :=
  fun _ hx => (mem_isolatorComm.1 hx).1

theorem commutator_le_isolatorComm (N : Subgroup G) [N.Normal] : ⁅N, N⁆ ≤ isolatorComm N := by
  intro x hx
  exact mem_isolatorComm.2 ⟨Subgroup.commutator_le_left N N hx, 1, one_pos, by simpa using hx⟩

instance isolatorComm_normal (N : Subgroup G) [N.Normal] : (isolatorComm N).Normal := by
  constructor
  intro x hx g
  obtain ⟨hxN, k, hk, hxk⟩ := mem_isolatorComm.1 hx
  refine mem_isolatorComm.2
    ⟨Subgroup.Normal.conj_mem (by infer_instance) x hxN g, k, hk, ?_⟩
  have hpow : (g * x * g⁻¹) ^ k = g * x ^ k * g⁻¹ := by simp [conj_pow]
  rw [hpow]
  exact Subgroup.Normal.conj_mem (by infer_instance) _ hxk g

/-- `N/C` is abelian for `C` the isolator, since `[N, N] ≤ C`. -/
instance isMulCommutative_map_isolatorComm (N : Subgroup G) [N.Normal] :
    IsMulCommutative (N.map (QuotientGroup.mk' (isolatorComm N))) := by
  constructor
  constructor
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨n, hn, rfl⟩ := hx
  obtain ⟨m, hm, rfl⟩ := hy
  apply Subtype.ext
  show (QuotientGroup.mk' (isolatorComm N) n) * (QuotientGroup.mk' (isolatorComm N) m)
      = (QuotientGroup.mk' (isolatorComm N) m) * (QuotientGroup.mk' (isolatorComm N) n)
  rw [← map_mul, ← map_mul]
  simp only [QuotientGroup.mk'_apply, QuotientGroup.eq]
  have hgr : (n * m)⁻¹ * (m * n) = ⁅m⁻¹, n⁻¹⁆ := by group
  rw [hgr]
  exact commutator_le_isolatorComm N
    (Subgroup.commutator_mem_commutator (N.inv_mem hm) (N.inv_mem hn))

/-- In a commutative group with no nontrivial element of finite order, powers are
injective. -/
theorem isMulTorsionFree_of_comm {A : Type*} [Group A] (hcomm : ∀ a c : A, a * c = c * a)
    (h : ∀ (a : A) (n : ℕ), n ≠ 0 → a ^ n = 1 → a = 1) : IsMulTorsionFree A := by
  constructor
  intro n hn a c hac
  have h1 : a ^ n = c ^ n := hac
  have hac' : Commute a c⁻¹ := hcomm a c⁻¹
  have hd : (a * c⁻¹) ^ n = 1 := by
    rw [hac'.mul_pow, h1, inv_pow, mul_inv_cancel]
  exact mul_inv_eq_one.1 (h _ n hn hd)

/-- **`N` modulo its isolator is torsion free** — this is why Lemma 2.1 applies to the pair
`isolatorComm N ≤ N` with no extra hypothesis. -/
instance isMulTorsionFree_map_isolatorComm (N : Subgroup G) [N.Normal] :
    IsMulTorsionFree (N.map (QuotientGroup.mk' (isolatorComm N))) := by
  haveI := isMulCommutative_map_isolatorComm N
  refine isMulTorsionFree_of_comm (fun a c => (IsMulCommutative.is_comm).comm a c) ?_
  rintro ⟨-, x, hxN, rfl⟩ n hn ha
  have hx : (QuotientGroup.mk' (isolatorComm N) x) ^ n = 1 := by
    have := congrArg (Subtype.val) ha
    simpa using this
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
  obtain ⟨-, k, hk, hxk⟩ := mem_isolatorComm.1 hx
  have hmem : x ∈ isolatorComm N :=
    mem_isolatorComm.2 ⟨hxN, n * k, Nat.mul_pos (Nat.pos_of_ne_zero hn) hk, by
      rw [pow_mul]; exact hxk⟩
  refine Subtype.ext ?_
  simpa using (QuotientGroup.eq_one_iff _).2 hmem

/-! ### The requirements pass to the isolator -/

variable {I J : Type*}

/-- **The integral requirements pass to the isolator of the commutator subgroup**, with no
torsion-freeness hypothesis. -/
theorem foxSat_isolatorComm (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (N : Subgroup G) [N.Normal]
    (h : ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v N) :
    ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v (isolatorComm N) := by
  rw [forall_foxSat_iff_injective b hcol]
  exact injective_boundaryMap_of_injective b hcol (isolatorComm N) N (isolatorComm_le N)
    ((forall_foxSat_iff_injective b hcol N).1 h)

/-- **The requirements modulo a prime pass to the isolator of the commutator subgroup.** -/
theorem foxSatMod_isolatorComm_prime (p : ℕ) [Fact p.Prime] (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (N : Subgroup G) [N.Normal]
    (h : ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod p b v N) :
    ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod p b v (isolatorComm N) := by
  rw [forall_foxSatMod_iff_injective p b hcol]
  exact injective_boundaryMapK_of_injective _ _ (isolatorComm N) N (isolatorComm_le N)
    ((forall_foxSatMod_iff_injective p b hcol N).1 h)

/-- The two cases at once: the requirement indexed by `m = 0` (integrally) or by a prime
`m = p` passes to the isolator. -/
theorem foxSatMod_isolatorComm (m : ℕ) (hm : m = 0 ∨ m.Prime)
    (b : I → J → MonoidAlgebra ℤ G) (hcol : ∀ j, {i | b i j ≠ 0}.Finite)
    (N : Subgroup G) [N.Normal]
    (h : ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod m b v N) :
    ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod m b v (isolatorComm N) := by
  rcases hm with rfl | hp
  · intro v
    exact (foxSatMod_zero_iff b v (isolatorComm N)).2
      (foxSat_isolatorComm b hcol N (fun w => (foxSatMod_zero_iff b w N).1 (h w)) v)
  · haveI := Fact.mk hp
    exact foxSatMod_isolatorComm_prime m b hcol N h

end FiniteChains
