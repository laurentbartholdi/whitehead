module

public import RequestProject.ChainFormula
public import RequestProject.FoxRequirementMod

@[expose] public section

/-!
# Formula (2.3) modulo an integer

`RequestProject/ChainFormula.lean` proves formula (2.3) of the paper for the integral
requirements: for a chain `K = X₀ ⊂ ⋯ ⊂ Xₙ` of two-complexes whose inclusions are zero on
`π₂`, and `M_r = ker (π₁(K) → π₁(X_r))`, a coefficient vector whose reduced Fox boundary
vanishes at stage `r` itself dies at stage `r + 1`.

Section 2 imposes the requirements (2.2) modulo every prime as well, and derives the
corresponding form of (2.3) with one extra ingredient, quoted from Hatcher: *a cycle modulo
`m` of the chain complex of the universal cover is congruent modulo `m` to an integral
cycle* (the universal cover of a two-complex has `H₁ = 0`).  That ingredient is the
hypothesis `CycleLiftsMod` below — like the other entries of `ChainInput` it is cell-level
topological data — and everything else is proved here: the analogue
`ChainInput.foxSatMod_of_not_foxSatMod` of formula (2.3) for the requirements modulo `m`.

Taking `m = 0` the statement specializes to the integral one, since `CycleLiftsMod 0` holds
trivially.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

universe u

variable {G : Type u} [Group G] {I J : Type u}

/-! ### Divisibility of coefficients and reduction along a homomorphism -/

theorem exists_nsmul_mapDomain_iff {A B : Type*} (psi : A → B) (hpsi : Function.Injective psi)
    (m : ℕ) (z : MonoidAlgebra ℤ A) :
    (∃ y : MonoidAlgebra ℤ B, MonoidAlgebra.mapDomain psi z = m • y) ↔
      ∃ y : MonoidAlgebra ℤ A, z = m • y := by
  classical
  constructor
  · rintro ⟨y, hy⟩
    rw [← dvd_coeff_iff_nsmul]
    intro q
    have hq : (MonoidAlgebra.mapDomain psi z).coeff (psi q) = z.coeff q := Finsupp.mapDomain_apply_of_injective hpsi z.coeff q
    refine ⟨y.coeff (psi q), ?_⟩
    rw [← hq, hy]
    show ((m • y : MonoidAlgebra ℤ B).coeff (psi q) : ℤ) = (m : ℤ) * y.coeff (psi q)
    rw [MonoidAlgebra.coeff_smul_apply, nsmul_eq_mul]
  · rintro ⟨y, rfl⟩
    refine ⟨MonoidAlgebra.mapDomain psi y, ?_⟩
    exact map_nsmul ((MonoidAlgebra.mapDomainLinearMap ℤ ℤ psi).toAddMonoidHom) m y

/-- The reduction of `x ∈ ℤ[G]` along a homomorphism `φ` is divisible by `m` exactly when
the reduction of `x` modulo `ker φ` is: the fibres of `φ` are the cosets of `ker φ`. -/
theorem vanishesModN_ker_iff {H : Type*} [Group H] (φ : G →* H) (m : ℕ)
    (x : MonoidAlgebra ℤ G) :
    VanishesModN m φ.ker x.coeff ↔ ∃ y, MonoidAlgebra.mapDomainRingHom ℤ φ x = m • y := by
  have hfact : MonoidAlgebra.mapDomainRingHom ℤ φ x
      = MonoidAlgebra.mapDomain (QuotientGroup.kerLift φ) (quotRingHom ℤ φ.ker x) := by
    apply MonoidAlgebra.coeff_injective
    change Finsupp.mapDomain _ x.coeff = Finsupp.mapDomain _ (Finsupp.mapDomain _ x.coeff)
    rw [← Finsupp.mapDomain_comp]
    rfl
  rw [vanishesModN_iff_nsmul, hfact,
    exists_nsmul_mapDomain_iff _ (QuotientGroup.kerLift_injective φ)]

/-! ### The lifting of cycles modulo `m` -/

variable {b : I → J → MonoidAlgebra ℤ G} {n : ℕ} {Fund : ℕ → Type u} [∀ r, Group (Fund r)]
  {Gen Cell : ℕ → Type u}

/-- **The input quoted from Hatcher.**  In the chain complex of the universal cover of
`X_r`, every chain whose boundary is divisible by `m` is congruent modulo `m` to a genuine
cycle. -/
def CycleLiftsMod (h : ChainInput b n Fund Gen Cell) (m : ℕ) : Prop :=
  ∀ r : ℕ, r < n → ∀ u : Cell r →₀ MonoidAlgebra ℤ (Fund r),
    (∀ a : Gen r, ∃ w, ∑ c ∈ u.support, u c * h.bdry r a c = m • w) →
      ∃ u' : Cell r →₀ MonoidAlgebra ℤ (Fund r),
        (∀ a : Gen r, ∑ c ∈ u'.support, u' c * h.bdry r a c = 0) ∧
          ∃ z : Cell r →₀ MonoidAlgebra ℤ (Fund r), u = u' + m • z

/-- For `m = 0` the lifting hypothesis is vacuous: a chain whose boundary is `0` is a
cycle. -/
theorem cycleLiftsMod_zero (h : ChainInput b n Fund Gen Cell) : CycleLiftsMod h 0 := by
  intro r _ u hu
  refine ⟨u, fun a => ?_, 0, by simp⟩
  obtain ⟨w, hw⟩ := hu a
  simpa using hw

namespace ChainInput

variable (h : ChainInput b n Fund Gen Cell)

/-- The additive map induced on chains by the inclusion `X_r ⊂ X_{r+1}`. -/
noncomputable def stepHom (r : ℕ) :
    (Cell r →₀ MonoidAlgebra ℤ (Fund r)) →+ (Cell (r + 1) →₀ MonoidAlgebra ℤ (Fund (r + 1))) :=
  (Finsupp.mapDomain.addMonoidHom (h.cellStep r)).comp
    (Finsupp.mapRange.addMonoidHom (MonoidAlgebra.mapDomainRingHom ℤ (h.psi r)).toAddMonoidHom)

theorem stepHom_apply (r : ℕ) (u : Cell r →₀ MonoidAlgebra ℤ (Fund r)) :
    h.stepHom r u =
      Finsupp.mapDomain (h.cellStep r)
        (Finsupp.mapRange (MonoidAlgebra.mapDomainRingHom ℤ (h.psi r)) (map_zero _) u) := rfl

/-- **The extension by zero of a vector whose reduced boundary vanishes modulo `m` is a
cycle modulo `m`.** -/
theorem oldVec_isCycleMod {r : ℕ} (m : ℕ) (v : J →₀ MonoidAlgebra ℤ G)
    (hv : ∀ i : I, VanishesModN m (h.phi r).ker (foxBoundary b v i).coeff) (a : Gen r) :
    ∃ w, ∑ c ∈ (h.oldVec r v).support, h.oldVec r v c * h.bdry r a c = m • w := by
  classical
  set u := h.oldVec r v with hu
  have hsub : u.support ⊆ v.support.image (h.cellIncl r) := h.oldVec_support_subset r v
  have hext : ∑ c ∈ u.support, u c * h.bdry r a c
      = ∑ c ∈ v.support.image (h.cellIncl r), u c * h.bdry r a c := by
    refine Finset.sum_subset hsub fun c _ hc => ?_
    rw [Finsupp.notMem_support_iff.mp hc, zero_mul]
  have himg : ∑ c ∈ v.support.image (h.cellIncl r), u c * h.bdry r a c
      = ∑ j ∈ v.support, u (h.cellIncl r j) * h.bdry r a (h.cellIncl r j) :=
    Finset.sum_image fun x _ y _ hxy => h.cellIncl_injective r hxy
  rw [hext, himg]
  by_cases hex : ∃ i, a = h.genIncl r i
  · obtain ⟨i, rfl⟩ := hex
    have hterm : ∀ j ∈ v.support,
        u (h.cellIncl r j) * h.bdry r (h.genIncl r i) (h.cellIncl r j)
          = MonoidAlgebra.mapDomainRingHom ℤ (h.phi r) (v j * b i j) := by
      intro j _
      rw [hu, h.oldVec_apply_cellIncl, h.bdry_old, ← map_mul]
    rw [Finset.sum_congr rfl hterm, ← map_sum]
    have hfox : ∑ j ∈ v.support, v j * b i j = foxBoundary b v i := rfl
    rw [hfox]
    exact (vanishesModN_ker_iff (h.phi r) m _).1 (hv i)
  · push_neg at hex
    refine ⟨0, ?_⟩
    rw [smul_zero]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [h.bdry_new r a hex j, mul_zero]

/-- **Formula (2.3) modulo `m`.**  If the reduced Fox boundary of `v` vanishes modulo `m`
at stage `r`, then `v` itself vanishes modulo `m` at stage `r + 1`. -/
theorem vanishesModN_succ {r : ℕ} (m : ℕ) (hlift : CycleLiftsMod h m) (hr : r < n)
    (v : J →₀ MonoidAlgebra ℤ G)
    (hv : ∀ i : I, VanishesModN m (h.phi r).ker (foxBoundary b v i).coeff) (j : J) :
    ∃ y, MonoidAlgebra.mapDomainRingHom ℤ (h.phi (r + 1)) (v j) = m • y := by
  classical
  obtain ⟨u', hu'cycle, z, hz⟩ := hlift r hr (h.oldVec r v) (h.oldVec_isCycleMod m v hv)
  have hzero : h.stepHom r u' = 0 := h.zero_pi2 r hr u' hu'cycle
  have hstep : h.stepHom r (h.oldVec r v) = m • h.stepHom r z := by
    rw [hz, map_add, hzero, zero_add, map_nsmul]
  have hcoord := DFunLike.congr_fun hstep (h.cellStep r (h.cellIncl r j))
  rw [stepHom_apply, Finsupp.mapDomain_apply_of_injective (h.cellStep_injective r)] at hcoord
  simp only [Finsupp.mapRange_apply] at hcoord
  rw [h.oldVec_apply_cellIncl, mapDomainRingHom_comp_apply, h.phi_succ] at hcoord
  exact ⟨(h.stepHom r z) (h.cellStep r (h.cellIncl r j)), by
    rw [hcoord]
    show ((m • h.stepHom r z : Cell (r + 1) →₀ MonoidAlgebra ℤ (Fund (r + 1)))
        (h.cellStep r (h.cellIncl r j)) : MonoidAlgebra ℤ (Fund (r + 1)))
      = m • (h.stepHom r z) (h.cellStep r (h.cellIncl r j))
    rw [Finsupp.smul_apply]⟩

/-- Once a vector has died modulo `m` at some stage, it stays dead at all later stages. -/
theorem vanishesModN_mono {r : ℕ} (m : ℕ) (x : MonoidAlgebra ℤ G)
    (hx : ∃ y, MonoidAlgebra.mapDomainRingHom ℤ (h.phi r) x = m • y) :
    ∀ s, r ≤ s → ∃ y, MonoidAlgebra.mapDomainRingHom ℤ (h.phi s) x = m • y := by
  have key : ∀ d : ℕ, ∃ y, MonoidAlgebra.mapDomainRingHom ℤ (h.phi (r + d)) x = m • y := by
    intro d
    induction d with
    | zero => simpa using hx
    | succ d ih =>
        obtain ⟨y, hy⟩ := ih
        have hstep : MonoidAlgebra.mapDomainRingHom ℤ
            ((h.psi (r + d)).comp (h.phi (r + d))) x
            = m • MonoidAlgebra.mapDomain (h.psi (r + d)) y := by
          rw [← mapDomainRingHom_comp_apply, hy]
          exact map_nsmul ((MonoidAlgebra.mapDomainRingHom ℤ (h.psi (r + d))).toAddMonoidHom) m y
        rw [h.phi_succ] at hstep
        exact ⟨_, hstep⟩
  intro s hs
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hs
  exact key d

/-- **Formula (2.3) modulo `m`, in the shape of the hypothesis `chain_subgroups`.**  A
requirement modulo `m` violated at stage `r` holds at every later stage. -/
theorem foxSatMod_of_not_foxSatMod (m : ℕ) (hlift : CycleLiftsMod h m)
    (v : J →₀ MonoidAlgebra ℤ G) (r : ℕ) (hviol : ¬ FoxSatMod m b v (h.phi r).ker) :
    ∀ s, r < s → s ≤ n → FoxSatMod m b v (h.phi s).ker := by
  intro s hrs hsn
  have hbdry : ∀ i : I, VanishesModN m (h.phi r).ker (foxBoundary b v i).coeff := by
    by_contra hcon
    exact hviol fun hb => absurd hb hcon
  have hr : r < n := lt_of_lt_of_le hrs hsn
  intro _ j
  have h1 := h.vanishesModN_succ m hlift hr v hbdry j
  exact (vanishesModN_ker_iff (h.phi s) m (v j)).2
    (h.vanishesModN_mono m (v j) h1 s (by omega))

end ChainInput

end FiniteChains
