module

public import Mathlib
public import RequestProject.FoxRequirementMod

@[expose] public section

/-!
# The requirements modulo `m` pass to the commutator subgroup

`RequestProject/FoxCommutator.lean` proves the integral half of the application of
Lemma 2.1 made at the end of Section 2: if the integral requirements (2.2) hold for a
normal subgroup `N` whose abelianization `N/[N,N]` is torsion free, then they hold for
`[N,N]`.  The paper imposes the requirements modulo every prime as well, and applies
Lemma 2.1 over `𝔽ₚ` in exactly the same way.  This file carries out that half.

The link between the two descriptions is the reduction of coefficients
`ℤ[G] → 𝔽ₚ[G]` (`coeffHom`): the requirement modulo `m` of
`RequestProject/FoxRequirementMod.lean`, stated as a divisibility of coset sums, is
precisely the statement that the Fox boundary of the reduced presentation matrix is
injective over `ZMod m` (`forall_foxSatMod_iff_injective`).  For `m = p` prime the
coefficients form a field, so Lemma 2.1 applies and gives
`foxSatMod_commutator`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

variable {G : Type*} [Group G] {I J : Type*}

/-! ### Reduction of coefficients `ℤ[G] → k[G]` -/

/-- Coefficientwise reduction of the group ring along the unique ring map `ℤ → k`. -/
noncomputable def coeffHom (k : Type*) [CommRing k] (H : Type*) [Group H] :
    MonoidAlgebra ℤ H →+* MonoidAlgebra k H :=
  MonoidAlgebra.mapRangeRingHom H (Int.castRingHom k)

variable {k : Type*} [CommRing k]

@[simp] theorem coeffHom_apply (x : MonoidAlgebra ℤ G) (g : G) :
    (coeffHom k G x).coeff g = ((x.coeff g : ℤ) : k) := by
  simp [coeffHom, MonoidAlgebra.mapRangeRingHom]

theorem quotRingHom_coeffHom (M : Subgroup G) [M.Normal] (x : MonoidAlgebra ℤ G) :
    quotRingHom k M (coeffHom k G x) = coeffHom k (G ⧸ M) (quotRingHom ℤ M x) := by
  apply MonoidAlgebra.coeff_injective
  change Finsupp.mapDomain (QuotientGroup.mk' M)
      (Finsupp.mapRange (fun a : ℤ => ((a : k))) (by simp) x.coeff)
    = Finsupp.mapRange (fun a : ℤ => ((a : k))) (by simp)
      (Finsupp.mapDomain (QuotientGroup.mk' M) x.coeff)
  exact Finsupp.mapDomain_mapRange _ _ _ _ (fun a b => by push_cast; ring)

theorem coeffHom_surjective_zmod (m : ℕ) :
    Function.Surjective (coeffHom (ZMod m) G) := by
  have h : Function.Surjective (fun a : ℤ => ((a : ZMod m))) := ZMod.intCast_surjective
  intro y
  obtain ⟨x, hx⟩ := Finsupp.mapRange_surjective (fun a : ℤ => ((a : ZMod m))) (by simp) h y.coeff
  exact ⟨MonoidAlgebra.ofCoeff x, MonoidAlgebra.coeff_injective hx⟩

/-- Coefficientwise reduction of a vector over `ℤ[G]` to a vector over `k[G]`. -/
noncomputable def coeffVec (k : Type*) [CommRing k] (H : Type*) [Group H] {J : Type*}
    (v : J →₀ MonoidAlgebra ℤ H) : J →₀ MonoidAlgebra k H :=
  Finsupp.mapRange (coeffHom k H) (map_zero _) v

@[simp] theorem coeffVec_apply (v : J →₀ MonoidAlgebra ℤ G) (j : J) :
    coeffVec k G v j = coeffHom k G (v j) := rfl

/-- Every vector over `ZMod m [G]` comes from a vector over `ℤ[G]`. -/
theorem exists_coeffVec (m : ℕ) (w : J →₀ MonoidAlgebra (ZMod m) G) :
    ∃ v : J →₀ MonoidAlgebra ℤ G, coeffVec (ZMod m) G v = w := by
  classical
  choose lift hlift using coeffHom_surjective_zmod (G := G) m
  refine ⟨Finsupp.mapRange (fun y => if y = 0 then 0 else lift y) (by simp) w, ?_⟩
  refine Finsupp.ext fun j => ?_
  simp only [coeffVec_apply, Finsupp.mapRange_apply]
  by_cases h : w j = 0 <;> simp [h, hlift]

/-! ### The reduced presentation matrix -/

/-- The Fox boundary matrix of the presentation, read over `k`. -/
noncomputable def bMod (k : Type*) [CommRing k] (H : Type*) [Group H] {I J : Type*}
    (b : I → J → MonoidAlgebra ℤ H) (i : I) (j : J) : MonoidAlgebra k H :=
  coeffHom k H (b i j)

theorem bMod_col_finite (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (j : J) : {i | bMod k G b i j ≠ 0}.Finite := by
  refine (hcol j).subset ?_
  intro i hi
  simp only [Set.mem_setOf_eq] at hi ⊢
  intro h
  exact hi (by simp [bMod, h])

theorem foxBoundaryK_bMod (b : I → J → MonoidAlgebra ℤ G) (v : J →₀ MonoidAlgebra ℤ G)
    (i : I) :
    foxBoundaryK k (bMod k G b) (coeffVec k G v) i = coeffHom k G (foxBoundary b v i) := by
  classical
  have hsupp : (coeffVec k G v).support ⊆ v.support := by
    intro j hj
    simp only [Finsupp.mem_support_iff, coeffVec_apply] at hj ⊢
    intro h
    exact hj (by rw [h, map_zero])
  rw [foxBoundaryK, foxBoundary, map_sum,
    Finset.sum_congr rfl (fun j (_ : j ∈ v.support) =>
      map_mul (coeffHom k G) (v j) (b i j))]
  refine Finset.sum_subset hsupp ?_
  intro j _ hj
  simp only [Finsupp.mem_support_iff, not_not, coeffVec_apply] at hj
  rw [coeffVec_apply, hj, zero_mul]

/-! ### The requirement modulo `m` is injectivity of the boundary over `ZMod m` -/

/-- Vanishing modulo `m` of a coefficient vector is vanishing of its reduction over
`ZMod m`. -/
theorem vanishesModN_iff_zmod (m : ℕ) (M : Subgroup G) [M.Normal] (x : MonoidAlgebra ℤ G) :
    VanishesModN m M x.coeff ↔ quotRingHom (ZMod m) M (coeffHom (ZMod m) G x) = 0 := by
  rw [vanishesModN_iff_dvd_coeff, quotRingHom_coeffHom]
  constructor
  · intro h
    apply MonoidAlgebra.coeff_injective
    refine Finsupp.ext fun q => ?_
    show (((quotRingHom ℤ M x).coeff q : ℤ) : ZMod m) = 0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (h q)
  · intro h q
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 ?_
    have := congrArg (fun z : MonoidAlgebra (ZMod m) (G ⧸ M) => z.coeff q) h
    simpa using this

/-- **The requirements modulo `m` are exactly the injectivity of the Fox boundary over
`ZMod m`.**  This is the analogue over `ZMod m` of
`FiniteChains.forall_foxSat_iff_injective`; for `m = 0` the two statements agree. -/
theorem forall_foxSatMod_iff_injective (m : ℕ) (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal] :
    (∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod m b v M) ↔
      Function.Injective
        (boundaryMapK (ZMod m) (bMod (ZMod m) G b) (bMod_col_finite b hcol) M) := by
  classical
  set bm := bMod (ZMod m) G b with hbm
  set hc := bMod_col_finite (k := ZMod m) b hcol with hhc
  have key : ∀ v : J →₀ MonoidAlgebra ℤ G, ∀ i : I,
      boundaryMapK (ZMod m) bm hc M (redVecK (ZMod m) M (coeffVec (ZMod m) G v)) i
        = quotRingHom (ZMod m) M (coeffHom (ZMod m) G (foxBoundary b v i)) := by
    intro v i
    rw [boundaryMapK_redVecK, foxBoundaryK_bMod]
  constructor
  · intro h
    rw [injective_iff_map_eq_zero]
    intro u hu
    obtain ⟨w, rfl⟩ := exists_liftK (k := ZMod m) M u
    obtain ⟨v, rfl⟩ := exists_coeffVec m w
    have hbd : ∀ i : I, VanishesModN m M (foxBoundary b v i).coeff := by
      intro i
      rw [vanishesModN_iff_zmod, ← key v i, hu]
      rfl
    have hv := h v hbd
    refine Finsupp.ext fun j => ?_
    rw [redVecK_apply, coeffVec_apply, Finsupp.coe_zero, Pi.zero_apply]
    exact (vanishesModN_iff_zmod m M (v j)).1 (hv j)
  · intro h v hbd j
    rw [vanishesModN_iff_zmod]
    have hzero : boundaryMapK (ZMod m) bm hc M (redVecK (ZMod m) M (coeffVec (ZMod m) G v)) = 0 := by
      refine Finsupp.ext fun i => ?_
      rw [key v i, Finsupp.coe_zero, Pi.zero_apply]
      exact (vanishesModN_iff_zmod m M _).1 (hbd i)
    have hz : redVecK (ZMod m) M (coeffVec (ZMod m) G v) = 0 := h (by rw [hzero, map_zero])
    have := congrArg (fun z : J →₀ MonoidAlgebra (ZMod m) (G ⧸ M) => z j) hz
    simpa using this

/-! ### Lemma 2.1 over `𝔽ₚ` -/

/-- **The requirements modulo a prime pass to the commutator subgroup.**  This is the
half modulo `p` of the application of Lemma 2.1 at the end of Section 2. -/
theorem foxSatMod_commutator (p : ℕ) [Fact p.Prime] (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (N : Subgroup G) [N.Normal]
    [IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆))]
    (h : ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod p b v N) :
    ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod p b v ⁅N, N⁆ := by
  have hle : ⁅N, N⁆ ≤ N := Subgroup.commutator_le_left N N
  rw [forall_foxSatMod_iff_injective p b hcol]
  exact injective_boundaryMapK_of_injective _ _ ⁅N, N⁆ N hle
    ((forall_foxSatMod_iff_injective p b hcol N).1 h)

end FiniteChains
