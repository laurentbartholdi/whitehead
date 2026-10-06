module

public import Mathlib
public import RequestProject.UniversalCoefficients

@[expose] public section

/-!
# The requirements (2.2) modulo an integer

The requirements (2.2) of the paper are imposed on a normal subgroup `M ◁ G` *integrally
and modulo every prime*: the reduced Fox boundary `∂_{2,M}` must not kill a nonzero vector,
neither over `ℤ[G/M]` nor over `𝔽ₚ[G/M]`.  `RequestProject/FoxRequirement.lean` formalizes
the integral half; this file formalizes the whole family at once.

For a natural number `m` the requirement modulo `m` says: if inside every coset of `M` the
coefficients of each coordinate of the Fox boundary of `v` add up to a multiple of `m`,
then the same holds for the coordinates of `v` itself (`FoxSatMod`).  Taking `m = 0` gives
back the integral requirement (`foxSatMod_zero_iff`), since being a multiple of `0` means
being `0`; taking `m = p` prime gives the requirement over `𝔽ₚ`.

Two things are proved here.

* `foxSatMod_finitelyDetermined` — each of these requirements depends on finitely many
  decisions `g ∈ M`, so that the compactness step of Section 2 applies to the whole family.
* `liftsMod_of_foxSatMod` — the requirement modulo `m` is exactly the lifting property
  `LiftsMod` of `RequestProject/UniversalCoefficients.lean` for the reduced Fox boundary.
  Consequently, if a normal subgroup satisfies the requirements modulo every prime, the
  cokernel of its Fox boundary is torsion free: the universal-coefficient input quoted at
  the end of Section 2 is *deduced from the requirements themselves*
  (`foxCokernel_torsionFree_of_foxSatMod`).
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open Finset

variable {G : Type*} [Group G]

/-! ### Vanishing modulo `m` of a coefficient vector -/

open scoped Classical in
/-- The reduction of `x ∈ ℤ[G]` to `ℤ[G/N]` is divisible by `m`: inside every coset of `N`
the coefficients of `x` add up to a multiple of `m`.  For `m = 0` this is `VanishesMod`. -/
def VanishesModN (m : ℕ) (N : Subgroup G) (x : G →₀ ℤ) : Prop :=
  ∀ g : G, (m : ℤ) ∣ ∑ h ∈ x.support.filter (fun h => h * g⁻¹ ∈ N), x h

@[simp] theorem vanishesModN_zero (m : ℕ) (N : Subgroup G) :
    VanishesModN m N (0 : G →₀ ℤ) := by
  classical
  intro g; simp

theorem vanishesModN_zero_iff (N : Subgroup G) (x : G →₀ ℤ) :
    VanishesModN 0 N x ↔ VanishesMod N x := by
  classical
  simp only [VanishesModN, VanishesMod, Nat.cast_zero, zero_dvd_iff]

/-- Whether the reduction of `x` vanishes modulo `m` only depends on the membership in `N`
of the finitely many quotients `h h'⁻¹` of elements of the support of `x`. -/
theorem vanishesModN_congr {m : ℕ} {x : G →₀ ℤ} {N N' : Subgroup G}
    (h : ∀ g ∈ x.support, ∀ g' ∈ x.support, (g * g'⁻¹ ∈ N ↔ g * g'⁻¹ ∈ N')) :
    VanishesModN m N x ↔ VanishesModN m N' x := by
  classical
  have main : ∀ M M' : Subgroup G,
      (∀ g ∈ x.support, ∀ g' ∈ x.support, (g * g'⁻¹ ∈ M ↔ g * g'⁻¹ ∈ M')) →
      VanishesModN m M x → VanishesModN m M' x := by
    intro M M' hMM' hM g
    by_cases hempty : (x.support.filter (fun h => h * g⁻¹ ∈ M')).Nonempty
    · obtain ⟨h₀, hh₀⟩ := hempty
      rw [mem_filter] at hh₀
      obtain ⟨hh₀supp, hh₀mem⟩ := hh₀
      have hfilter : x.support.filter (fun h => h * g⁻¹ ∈ M')
          = x.support.filter (fun h => h * h₀⁻¹ ∈ M) := by
        refine filter_congr fun h hh => ?_
        constructor
        · intro hmem
          have : h * h₀⁻¹ ∈ M' := by
            have : h * h₀⁻¹ = (h * g⁻¹) * (h₀ * g⁻¹)⁻¹ := by group
            rw [this]
            exact M'.mul_mem hmem (M'.inv_mem hh₀mem)
          exact (hMM' h hh h₀ hh₀supp).mpr this
        · intro hmem
          have hM' : h * h₀⁻¹ ∈ M' := (hMM' h hh h₀ hh₀supp).mp hmem
          have : h * g⁻¹ = (h * h₀⁻¹) * (h₀ * g⁻¹) := by group
          rw [this]
          exact M'.mul_mem hM' hh₀mem
      rw [hfilter]
      exact hM h₀
    · rw [Finset.not_nonempty_iff_eq_empty] at hempty
      rw [hempty, Finset.sum_empty]
      exact dvd_zero _
  exact ⟨main N N' h, main N' N fun g hg g' hg' => (h g hg g' hg').symm⟩

variable {I J : Type*}

/-- The requirement (2.2) modulo `m`, attached to the coefficient vector `v`: if the
reduced boundary of `v` is divisible by `m`, then so is the reduced `v`. -/
def FoxSatMod (m : ℕ) (b : I → J → MonoidAlgebra ℤ G) (v : J →₀ MonoidAlgebra ℤ G)
    (N : Subgroup G) : Prop :=
  (∀ i : I, VanishesModN m N (foxBoundary b v i).coeff) → ∀ j : J, VanishesModN m N (v j).coeff

/-- For `m = 0` the requirement modulo `m` is the integral requirement. -/
theorem foxSatMod_zero_iff (b : I → J → MonoidAlgebra ℤ G) (v : J →₀ MonoidAlgebra ℤ G)
    (N : Subgroup G) : FoxSatMod 0 b v N ↔ FoxSat b v N := by
  simp only [FoxSatMod, FoxSat, vanishesModN_zero_iff]

/-- **Each requirement modulo `m` depends on finitely many membership decisions.** -/
theorem foxSatMod_finitelyDetermined (m : ℕ) (b : I → J → MonoidAlgebra ℤ G)
    (v : J →₀ MonoidAlgebra ℤ G) (hfin : {i : I | foxBoundary b v i ≠ 0}.Finite) :
    ∃ F : Finset G, ∀ N N' : Subgroup G,
      (∀ g ∈ F, (g ∈ N ↔ g ∈ N')) → (FoxSatMod m b v N ↔ FoxSatMod m b v N') := by
  classical
  set S : Finset G :=
    (v.support.biUnion fun j => (v j).coeff.support) ∪
      (hfin.toFinset.biUnion fun i => (foxBoundary b v i).coeff.support) with hS
  refine ⟨(S ×ˢ S).image (fun p => p.1 * p.2⁻¹), ?_⟩
  intro N N' hagree
  have hpair : ∀ g ∈ S, ∀ g' ∈ S, (g * g'⁻¹ ∈ N ↔ g * g'⁻¹ ∈ N') := by
    intro g hg g' hg'
    exact hagree _ (Finset.mem_image.mpr ⟨(g, g'), Finset.mem_product.mpr ⟨hg, hg'⟩, rfl⟩)
  have hvsupp : ∀ j : J, (v j).coeff.support ⊆ S := by
    intro j g hg
    by_cases hj : j ∈ v.support
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, hj, hg⟩)
    · rw [Finsupp.notMem_support_iff.mp hj] at hg
      simp at hg
  have hbsupp : ∀ i : I, (foxBoundary b v i).coeff.support ⊆ S := by
    intro i g hg
    by_cases hi : foxBoundary b v i = 0
    · rw [hi] at hg; simp at hg
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, ?_, hg⟩)
      simpa [Set.Finite.mem_toFinset] using hi
  have hv : ∀ j : J, (VanishesModN m N (v j).coeff ↔ VanishesModN m N' (v j).coeff) := fun j =>
    vanishesModN_congr fun g hg g' hg' => hpair g (hvsupp j hg) g' (hvsupp j hg')
  have hb : ∀ i : I,
      (VanishesModN m N (foxBoundary b v i).coeff ↔ VanishesModN m N' (foxBoundary b v i).coeff) :=
    fun i => vanishesModN_congr fun g hg g' hg' => hpair g (hbsupp i hg) g' (hbsupp i hg')
  constructor
  · intro hSat hbdry j
    exact (hv j).mp (hSat (fun i => (hb i).mpr (hbdry i)) j)
  · intro hSat hbdry j
    exact (hv j).mpr (hSat (fun i => (hb i).mp (hbdry i)) j)

/-! ### The requirement modulo `m` as a divisibility statement in `ℤ[G/N]` -/

open scoped Classical in
/-- The coefficient of the reduction of `x` at the coset of `g` is the sum of the
coefficients of `x` over that coset. -/
theorem quotRingHom_apply_mk (M : Subgroup G) [M.Normal] (x : MonoidAlgebra ℤ G) (g : G) :
    (quotRingHom ℤ M x).coeff ((g : G ⧸ M)) = ∑ h ∈ x.coeff.support.filter (fun h => h * g⁻¹ ∈ M), x.coeff h := by
  classical
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

/-- Vanishing modulo `m` means that every coefficient of the reduction is divisible by
`m`. -/
theorem vanishesModN_iff_dvd_coeff (m : ℕ) (M : Subgroup G) [M.Normal]
    (x : MonoidAlgebra ℤ G) :
    VanishesModN m M x.coeff ↔ ∀ q : G ⧸ M, (m : ℤ) ∣ (quotRingHom ℤ M x).coeff q := by
  classical
  constructor
  · intro h q
    induction q using QuotientGroup.induction_on with
    | H g => rw [quotRingHom_apply_mk]; exact h g
  · intro h g
    rw [← quotRingHom_apply_mk M x g]
    exact h _

/-- Coefficientwise division by `m`. -/
noncomputable def divCoeff (m : ℕ) {H : Type*} (z : MonoidAlgebra ℤ H) : MonoidAlgebra ℤ H :=
  MonoidAlgebra.ofCoeff (Finsupp.mapRange (fun a : ℤ => a / (m : ℤ)) (by simp) z.coeff)

/-- An element all of whose coefficients are divisible by `m` is `m` times an element. -/
theorem nsmul_divCoeff (m : ℕ) {H : Type*} (z : MonoidAlgebra ℤ H)
    (hz : ∀ q : H, (m : ℤ) ∣ z.coeff q) : m • divCoeff m z = z := by
  apply MonoidAlgebra.coeff_injective
  refine Finsupp.ext fun q => ?_
  show m • (divCoeff m z).coeff q = z.coeff q
  rw [divCoeff, MonoidAlgebra.coeff_ofCoeff, Finsupp.mapRange_apply, nsmul_eq_mul]
  exact Int.mul_ediv_cancel' (hz q)

/-- Divisibility of all coefficients by `m` means being `m` times an element. -/
theorem dvd_coeff_iff_nsmul (m : ℕ) {H : Type*} (z : MonoidAlgebra ℤ H) :
    (∀ q : H, (m : ℤ) ∣ z.coeff q) ↔ ∃ y : MonoidAlgebra ℤ H, z = m • y := by
  constructor
  · intro h
    exact ⟨divCoeff m z, (nsmul_divCoeff m z h).symm⟩
  · rintro ⟨y, rfl⟩ q
    refine ⟨y.coeff q, ?_⟩
    show ((m • y : MonoidAlgebra ℤ H).coeff q : ℤ) = (m : ℤ) * y.coeff q
    rw [MonoidAlgebra.coeff_smul_apply, nsmul_eq_mul]

/-- Vanishing modulo `m` in the form used in the chain argument: the reduction is `m` times
an element. -/
theorem vanishesModN_iff_nsmul (m : ℕ) (M : Subgroup G) [M.Normal] (x : MonoidAlgebra ℤ G) :
    VanishesModN m M x.coeff ↔ ∃ y, quotRingHom ℤ M x = m • y := by
  rw [vanishesModN_iff_dvd_coeff, dvd_coeff_iff_nsmul]

/-! ### The requirements modulo `m` are the lifting property of the Fox boundary -/

variable (b : I → J → MonoidAlgebra ℤ G)

/-- **The requirement modulo `m`, in the form used by the universal-coefficient
argument.**  If all requirements modulo `m` hold at `N`, then the reduced Fox boundary is
injective modulo `m`: whenever its value on a vector is divisible by `m`, the vector itself
is. -/
theorem liftsMod_of_foxSatMod (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (N : Subgroup G)
    [N.Normal] (m : ℕ) (h : ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod m b v N) :
    LiftsMod (boundaryMap b hcol N).toAddMonoidHom m := by
  classical
  rintro u ⟨w, hw⟩
  obtain ⟨v, rfl⟩ := exists_lift N u
  have hbd : ∀ i : I, VanishesModN m N (foxBoundary b v i).coeff := by
    intro i
    rw [vanishesModN_iff_dvd_coeff]
    intro q
    have hcoord : quotRingHom ℤ N (foxBoundary b v i) = m • w i := by
      rw [← boundaryMap_redVec b hcol N v i]
      have := congrArg (fun z : I →₀ MonoidAlgebra ℤ (G ⧸ N) => z i) hw
      simpa using this
    rw [hcoord]
    exact ⟨(w i).coeff q, by
      show ((m • w i : MonoidAlgebra ℤ (G ⧸ N)).coeff q : ℤ) = (m : ℤ) * (w i).coeff q
      rw [MonoidAlgebra.coeff_smul_apply, nsmul_eq_mul]⟩
  have hv := h v hbd
  refine ⟨Finsupp.mapRange (divCoeff m) (by simp [divCoeff]) (redVec N v), ?_⟩
  refine Finsupp.ext fun j => ?_
  show redVec N v j = m • (Finsupp.mapRange (divCoeff m) _ (redVec N v)) j
  rw [Finsupp.mapRange_apply]
  refine (nsmul_divCoeff m (redVec N v j) ?_).symm
  intro q
  have := (vanishesModN_iff_dvd_coeff m N (v j)).1 (hv j) q
  simpa [redVec_apply] using this

/-- **The universal-coefficient input, deduced from the requirements.**  If a normal
subgroup satisfies the requirements (2.2) modulo every prime, then the cokernel of its
reduced Fox boundary — which contains the first homology of the cover `K_N` — is torsion
free. -/
theorem foxCokernel_torsionFree_of_foxSatMod (hcol : ∀ j, {i | b i j ≠ 0}.Finite)
    (N : Subgroup G) [N.Normal]
    (h : ∀ (p : ℕ), p.Prime → ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod p b v N) :
    IsAddTorsionFree (foxCokernel b hcol N) :=
  foxCokernel_torsionFree b hcol N fun p hp => liftsMod_of_foxSatMod b hcol N p (h p hp)

end FiniteChains
