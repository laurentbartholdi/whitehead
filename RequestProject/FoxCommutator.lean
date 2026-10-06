module

public import Mathlib
public import RequestProject.FoxRequirement
public import RequestProject.BoundaryRing

@[expose] public section

/-!
# The requirements pass to the commutator subgroup (Lemma 2.1 in the paper's application)

Section 2 applies Lemma 2.1 with `Q = G/[N,N]`, `H = N/[N,N]` and `f = ∂_{2,[N,N]}` to
conclude that, if the requirements (2.2) hold for a normal subgroup `N` and `N/[N,N]` is
torsion free, then they also hold for `[N,N]`.

This file carries out that application.  The requirements are the ones formalized in
`RequestProject/FoxRequirement.lean`, and the algebraic input is the unconditional Lemma 2.1
of `RequestProject/LemmaTwoOne.lean`.
-/

open scoped commutatorElement

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

variable {G : Type*} [Group G] {I J : Type*}

/-- Coefficientwise reduction of a vector over `ℤ[G]` to a vector over `ℤ[G/M]`. -/
noncomputable def redVec (M : Subgroup G) [M.Normal] (v : J →₀ MonoidAlgebra ℤ G) :
    J →₀ MonoidAlgebra ℤ (G ⧸ M) :=
  redVecK ℤ M v

@[simp] theorem redVec_apply (M : Subgroup G) [M.Normal] (v : J →₀ MonoidAlgebra ℤ G) (j : J) :
    redVec M v j = quotRingHom ℤ M (v j) := rfl

/-- The `j`-th column of the reduced boundary matrix. -/
noncomputable def boundaryCol (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal] (j : J) :
    I →₀ MonoidAlgebra ℤ (G ⧸ M) :=
  boundaryColK ℤ b hcol M j

@[simp] theorem boundaryCol_apply (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal] (j : J) (i : I) :
    boundaryCol b hcol M j i = quotRingHom ℤ M (b i j) := rfl

/-- The Fox boundary `∂_{2,M}` as a map of free left `ℤ[G/M]`-modules. -/
noncomputable def boundaryMap (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal] :
    (J →₀ MonoidAlgebra ℤ (G ⧸ M)) →ₗ[MonoidAlgebra ℤ (G ⧸ M)]
      (I →₀ MonoidAlgebra ℤ (G ⧸ M)) :=
  boundaryMapK ℤ b hcol M

theorem boundaryMap_apply_coord (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal]
    (u : J →₀ MonoidAlgebra ℤ (G ⧸ M)) (i : I) :
    boundaryMap b hcol M u i = ∑ j ∈ u.support, u j * quotRingHom ℤ M (b i j) :=
  boundaryMapK_apply_coord b hcol M u i

/-- The Fox boundary of `RequestProject/FoxRequirement.lean` is the case `k = ℤ`. -/
theorem foxBoundary_eq_foxBoundaryK (b : I → J → MonoidAlgebra ℤ G)
    (v : J →₀ MonoidAlgebra ℤ G) (i : I) : foxBoundary b v i = foxBoundaryK ℤ b v i := rfl

theorem boundaryMap_redVec (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal]
    (v : J →₀ MonoidAlgebra ℤ G) (i : I) :
    boundaryMap b hcol M (redVec M v) i = quotRingHom ℤ M (foxBoundary b v i) :=
  boundaryMapK_redVecK b hcol M v i

/-- Reduction of `x ∈ ℤ[G]` vanishes exactly when, inside every coset of `M`, the
coefficients of `x` add up to zero. -/
theorem vanishesMod_iff_quotRingHom_eq_zero (M : Subgroup G) [M.Normal] (x : MonoidAlgebra ℤ G) :
    VanishesMod M x.coeff ↔ quotRingHom ℤ M x = 0 := by
  classical
  have hval : ∀ g : G, (quotRingHom ℤ M x).coeff ((g : G ⧸ M)) =
      ∑ h ∈ x.coeff.support.filter (fun h => h * g⁻¹ ∈ M), x.coeff h := by
    intro g
    show (Finsupp.mapDomain (QuotientGroup.mk' M) x.coeff) (g : G ⧸ M) = _
    rw [Finsupp.mapDomain, Finsupp.sum, Finsupp.finsetSum_apply, Finset.sum_filter]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finsupp.single_apply]
    congr 1
    simp only [eq_iff_iff, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    constructor
    · intro hh
      have h1 : g⁻¹ * h ∈ M := by simpa using M.inv_mem hh
      have h2 := Subgroup.Normal.conj_mem (by infer_instance) _ h1 h
      have hgr : h * (g⁻¹ * h) * h⁻¹ = h * g⁻¹ := by group
      rwa [hgr] at h2
    · intro hh
      have h1 : g * h⁻¹ ∈ M := by simpa using M.inv_mem hh
      have h2 := Subgroup.Normal.conj_mem (by infer_instance) _ h1 h⁻¹
      have hgr : h⁻¹ * (g * h⁻¹) * h⁻¹⁻¹ = h⁻¹ * g := by group
      rwa [hgr] at h2
  constructor
  · intro h
    ext q
    induction q using QuotientGroup.induction_on with
    | H g => rw [hval g]; simpa using h g
  · intro h g
    rw [← hval g, h]
    simp

/-- Reduction of coefficient vectors is surjective. -/
theorem quotRingHom_surjective (M : Subgroup G) [M.Normal] :
    Function.Surjective (quotRingHom ℤ M) := quotRingHomK_surjective M

/-- Every vector over `ℤ[G/M]` lifts to a vector over `ℤ[G]`. -/
theorem exists_lift (M : Subgroup G) [M.Normal] (u : J →₀ MonoidAlgebra ℤ (G ⧸ M)) :
    ∃ v : J →₀ MonoidAlgebra ℤ G, redVec M v = u := exists_liftK M u

/-- The requirements attached to all coefficient vectors hold at `M` exactly when the
reduced boundary map is injective. -/
theorem forall_foxSat_iff_injective (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal] :
    (∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v M) ↔
      Function.Injective (boundaryMap b hcol M) := by
  classical
  constructor
  · intro h
    rw [injective_iff_map_eq_zero]
    intro u hu
    obtain ⟨v, rfl⟩ := exists_lift M u
    have hbd : ∀ i, VanishesMod M (foxBoundary b v i).coeff := by
      intro i
      rw [vanishesMod_iff_quotRingHom_eq_zero, ← boundaryMap_redVec b hcol M v i, hu]
      rfl
    have hv := h v hbd
    refine Finsupp.ext fun j => ?_
    rw [redVec_apply, Finsupp.coe_zero, Pi.zero_apply]
    exact (vanishesMod_iff_quotRingHom_eq_zero M (v j)).1 (hv j)
  · intro h v hbd j
    rw [vanishesMod_iff_quotRingHom_eq_zero]
    have hu : boundaryMap b hcol M (redVec M v) = 0 := by
      refine Finsupp.ext fun i => ?_
      rw [boundaryMap_redVec, Finsupp.coe_zero, Pi.zero_apply]
      exact (vanishesMod_iff_quotRingHom_eq_zero M _).1 (hbd i)
    have hz : redVec M v = 0 := h (by rw [hu, map_zero])
    have := congrArg (fun w : J →₀ MonoidAlgebra ℤ (G ⧸ M) => w j) hz
    simpa using this

/-- **Lemma 2.1 for a pair of normal subgroups.**  If `C ≤ N` are normal subgroups of `G`
with `N/C` torsion-free abelian, then injectivity of the boundary reduced modulo `N`
implies injectivity of the boundary reduced modulo `C`.  This is the case `k = ℤ` of
`FiniteChains.injective_boundaryMapK_of_injective`. -/
theorem injective_boundaryMap_of_injective (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (C N : Subgroup G) [C.Normal] [N.Normal]
    (hCN : C ≤ N)
    [IsMulCommutative (N.map (QuotientGroup.mk' C))]
    [IsMulTorsionFree (N.map (QuotientGroup.mk' C))]
    (h : Function.Injective (boundaryMap b hcol N)) :
    Function.Injective (boundaryMap b hcol C) :=
  injective_boundaryMapK_of_injective b hcol C N hCN h

/-- The image of `N` in `G/[N,N]`, that is `N/[N,N]`, is abelian. -/
instance isMulCommutative_map_commutator (N : Subgroup G) [N.Normal] :
    IsMulCommutative (N.map (QuotientGroup.mk' ⁅N, N⁆)) := by
  constructor
  constructor
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨n, hn, rfl⟩ := hx
  obtain ⟨m, hm, rfl⟩ := hy
  apply Subtype.ext
  show (QuotientGroup.mk' ⁅N, N⁆ n) * (QuotientGroup.mk' ⁅N, N⁆ m)
      = (QuotientGroup.mk' ⁅N, N⁆ m) * (QuotientGroup.mk' ⁅N, N⁆ n)
  rw [← map_mul, ← map_mul]
  simp only [QuotientGroup.mk'_apply, QuotientGroup.eq]
  have hgr : (n * m)⁻¹ * (m * n) = ⁅m⁻¹, n⁻¹⁆ := by group
  rw [hgr]
  exact Subgroup.commutator_mem_commutator (N.inv_mem hm) (N.inv_mem hn)

/-- **The requirements pass to the commutator subgroup.**  If every requirement (2.2) holds
for the normal subgroup `N` and `N/[N,N]` is torsion free, then every requirement holds for
`[N,N]`. -/
theorem foxSat_commutator (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (N : Subgroup G) [N.Normal]
    [IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆))]
    (h : ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v N) :
    ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v ⁅N, N⁆ := by
  have hle : ⁅N, N⁆ ≤ N := Subgroup.commutator_le_left N N
  rw [forall_foxSat_iff_injective b hcol]
  exact injective_boundaryMap_of_injective b hcol ⁅N, N⁆ N hle
    ((forall_foxSat_iff_injective b hcol N).1 h)

/-- The same statement in the shape in which Section~2 uses it, and in which it appears as
the hypothesis `sat_commutator` of `FiniteChains.NecessityInputs`: for the Fox requirements
that hypothesis is a theorem, given only that the quotients `N/[N,N]` are torsion free. -/
theorem foxSat_commutator_forall (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite)
    (htf : ∀ (N : Subgroup G) [N.Normal],
      IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆))) :
    ∀ (N : Subgroup G) [N.Normal], (∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v N) →
      ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v ⁅N, N⁆ := by
  intro N _ h
  haveI := htf N
  exact foxSat_commutator b hcol N h

end FiniteChains
