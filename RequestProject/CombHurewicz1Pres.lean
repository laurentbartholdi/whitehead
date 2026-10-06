import RequestProject.CombPresPi1

/-!
# Hurewicz in degree one for a presentation complex

For a two-complex `K` the first homology is `H₁(K) = ker ∂₁ / im ∂₂` and the Hurewicz theorem
in degree one says that it is the abelianization of `π₁(K)`.  For the presentation complex
`K = presComplex ρ` of `⟨x_i | r_j⟩` everything is explicit: `K` has a single vertex, so
`∂₁ = 0` and `C₁ = (α →₀ ℤ)`, the class of an edge loop is the exponent-sum vector of the word
it spells, and `im ∂₂` is spanned by the exponent-sum vectors of the relators.

This file proves the corresponding statement:

* `FiniteChains.Comb.expVec` — the exponent-sum homomorphism `F → (α →₀ ℤ)`, with
  `FiniteChains.Comb.ker_expVec` : its kernel is exactly the commutator subgroup of `F`
  (so `(α →₀ ℤ)` is the abelianization of the free group) and
  `FiniteChains.Comb.expVec_surjective`;
* `FiniteChains.Comb.expVec_pathChain` — the exponent-sum vector of a word is the one-chain
  carried by the corresponding edge loop of `presComplex ρ`;
* `FiniteChains.Comb.bdry1_presComplex` — `∂₁ = 0` and `FiniteChains.Comb.cycles1_pres` —
  every one-chain of `presComplex ρ` is a cycle;
* `FiniteChains.Comb.expVec_mem_range_iff` — **the Hurewicz statement**: a word spells a
  one-boundary exactly when it lies in `R·[F, F]`, that is, exactly when its class in
  `π₁(K) = F/R` lies in the commutator subgroup.
-/

namespace FiniteChains
namespace Comb

universe u

variable {α : Type u} [DecidableEq α] {J : Type u}

/-! ### The exponent-sum homomorphism -/

/-- The exponent-sum vector of a word in the free group. -/
noncomputable def expVec : FreeGroup α →* Multiplicative (α →₀ ℤ) :=
  FreeGroup.lift fun a => Multiplicative.ofAdd (Finsupp.single a (1 : ℤ))

omit [DecidableEq α] in
@[simp] theorem expVec_of (a : α) :
    expVec (FreeGroup.of a) = Multiplicative.ofAdd (Finsupp.single a (1 : ℤ)) := by
  simp [expVec]

omit [DecidableEq α] in
theorem pathChain_append (l l' : List (α × Bool)) :
    pathChain (l ++ l') = pathChain l + pathChain l' := by
  simp [pathChain]

omit [DecidableEq α] in
theorem expVec_single_germ (x : α × Bool) :
    expVec (FreeGroup.mk [x]) = Multiplicative.ofAdd (pathChain [x]) := by
  obtain ⟨a, b⟩ := x
  cases b
  · have h1 : FreeGroup.mk [(a, false)] = (FreeGroup.of a)⁻¹ := rfl
    rw [h1, map_inv, expVec_of]
    show Multiplicative.ofAdd (-Finsupp.single a (1 : ℤ)) = _
    rw [pathChain_cons]
    simp
  · have h1 : FreeGroup.mk [(a, true)] = FreeGroup.of a := rfl
    rw [h1, expVec_of, pathChain_cons]
    simp

omit [DecidableEq α] in
/-- The exponent-sum vector of a word is the one-chain carried by the edge path spelling
it. -/
theorem expVec_pathChain (L : List (α × Bool)) :
    expVec (FreeGroup.mk L) = Multiplicative.ofAdd (pathChain L) := by
  induction L with
  | nil => simp [expVec, pathChain]
  | cons x L ih =>
      rw [show (x :: L) = [x] ++ L from rfl, ← FreeGroup.mul_mk, map_mul, ih,
        pathChain_append, expVec_single_germ]
      rfl

/-- The inverse of the abelianization map, on the level of exponent vectors. -/
noncomputable def expVecInv : (α →₀ ℤ) →+ Additive (Abelianization (FreeGroup α)) :=
  Finsupp.liftAddHom fun a =>
    (zmultiplesHom (Additive (Abelianization (FreeGroup α))))
      (Additive.ofMul (Abelianization.of (FreeGroup.of a)))

omit [DecidableEq α] in
theorem expVecInv_expVec (w : FreeGroup α) :
    expVecInv (Multiplicative.toAdd (expVec w)) = Additive.ofMul (Abelianization.of w) := by
  refine FreeGroup.induction_on w ?_ ?_ ?_ ?_
  · simp
  · intro a
    simp [expVecInv]
  · intro a ih
    have h : Multiplicative.toAdd (expVec (FreeGroup.of a)⁻¹)
        = -Multiplicative.toAdd (expVec (FreeGroup.of a)) := by
      rw [map_inv]; rfl
    rw [h, map_neg, ih, map_inv]
    rfl
  · intro x y hx hy
    have h : Multiplicative.toAdd (expVec (x * y))
        = Multiplicative.toAdd (expVec x) + Multiplicative.toAdd (expVec y) := by
      rw [map_mul]; rfl
    rw [h, map_add, hx, hy, map_mul]
    rfl

omit [DecidableEq α] in
/-- **The abelianization of the free group is the group of exponent vectors**: the kernel of
the exponent-sum homomorphism is the commutator subgroup. -/
theorem ker_expVec : (expVec (α := α)).ker = commutator (FreeGroup α) := by
  refine le_antisymm ?_ (Abelianization.commutator_subset_ker _)
  intro w hw
  have hw' : expVec w = 1 := hw
  have h : Additive.ofMul (Abelianization.of w) = 0 := by
    rw [← expVecInv_expVec w, hw']
    simp
  have h1 : Abelianization.of w = 1 := h
  rw [← Abelianization.ker_of (FreeGroup α)]
  exact h1

omit [DecidableEq α] in
theorem expVec_surjective : Function.Surjective (expVec (α := α)) := by
  intro c
  obtain ⟨v, hv⟩ : ∃ v : α →₀ ℤ, v = Multiplicative.toAdd c := ⟨_, rfl⟩
  suffices h : ∀ v : α →₀ ℤ, ∃ w : FreeGroup α, expVec w = Multiplicative.ofAdd v by
    obtain ⟨w, hw⟩ := h v
    exact ⟨w, by rw [hw, hv]; rfl⟩
  intro v
  induction v using Finsupp.induction_linear with
  | zero => exact ⟨1, by simp⟩
  | add v₁ v₂ h₁ h₂ =>
      obtain ⟨w₁, hw₁⟩ := h₁
      obtain ⟨w₂, hw₂⟩ := h₂
      exact ⟨w₁ * w₂, by rw [map_mul, hw₁, hw₂]; rfl⟩
  | single a n =>
      refine ⟨FreeGroup.of a ^ n, ?_⟩
      rw [map_zpow, expVec_of]
      show Multiplicative.ofAdd (n • Finsupp.single a (1 : ℤ)) = _
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]

/-! ### The presentation complex -/

variable (ρ : J → FreeGroup α)

@[simp] theorem bdry1_presComplex (c : α →₀ ℤ) : bdry1 (presComplex ρ) c = 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, h₁, h₂, add_zero]
  | single a n => simp [bdry1]

/-- Every one-chain of the presentation complex is a cycle: the complex has one vertex. -/
theorem cycles1_pres : LinearMap.ker (bdry1 (presComplex ρ)) = ⊤ := by
  refine eq_top_iff.mpr ?_
  intro c _
  exact bdry1_presComplex ρ c

theorem bdry2_pres_single (j : J) :
    bdry2 (presComplex ρ) (Finsupp.single j (1 : ℤ))
      = Multiplicative.toAdd (expVec (ρ j)) := by
  rw [bdry2_single, one_smul]
  have h : (presComplex ρ).att j = (ρ j).toWord := rfl
  rw [h]
  conv_rhs => rw [← FreeGroup.mk_toWord (x := ρ j)]
  rw [expVec_pathChain]
  rfl

/-- The one-boundaries of the presentation complex, viewed as a subgroup of the group of
exponent vectors. -/
noncomputable def bdrySub : Subgroup (Multiplicative (α →₀ ℤ)) :=
  AddSubgroup.toSubgroup (LinearMap.range (bdry2 (presComplex ρ))).toAddSubgroup

theorem mem_bdrySub_iff (c : α →₀ ℤ) :
    Multiplicative.ofAdd c ∈ bdrySub ρ ↔ c ∈ LinearMap.range (bdry2 (presComplex ρ)) :=
  Iff.rfl

/-- Every relator spells a one-boundary, and so does every element of the relator
subgroup. -/
theorem relSub_le_comap_bdrySub : relSub ρ ≤ Subgroup.comap expVec (bdrySub ρ) := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro x ⟨j, rfl⟩
  show expVec (ρ j) ∈ bdrySub ρ
  have h : Multiplicative.ofAdd (Multiplicative.toAdd (expVec (ρ j))) ∈ bdrySub ρ := by
    rw [mem_bdrySub_iff, ← bdry2_pres_single ρ j]
    exact LinearMap.mem_range.mpr ⟨Finsupp.single j (1 : ℤ), rfl⟩
  exact h

/-- Every one-boundary is spelled by an element of the relator subgroup. -/
theorem exists_relator_expVec (c : J →₀ ℤ) :
    ∃ r ∈ relSub ρ, Multiplicative.toAdd (expVec r) = bdry2 (presComplex ρ) c := by
  induction c using Finsupp.induction_linear with
  | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
  | add c₁ c₂ h₁ h₂ =>
      obtain ⟨r₁, hr₁, he₁⟩ := h₁
      obtain ⟨r₂, hr₂, he₂⟩ := h₂
      refine ⟨r₁ * r₂, Subgroup.mul_mem _ hr₁ hr₂, ?_⟩
      rw [map_mul, map_add, ← he₁, ← he₂]
      rfl
  | single j n =>
      have hmem : ρ j ∈ relSub ρ := Subgroup.subset_normalClosure (Set.mem_range_self j)
      refine ⟨ρ j ^ n, Subgroup.zpow_mem _ hmem n, ?_⟩
      have hsm : Finsupp.single j n = n • Finsupp.single j (1 : ℤ) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [map_zpow, hsm, map_zsmul, bdry2_pres_single ρ j]
      rfl

/-- **Hurewicz in degree one for a presentation complex.**  A word spells a one-boundary of
`presComplex ρ` exactly when it lies in `R·[F, F]`; equivalently, the Hurewicz homomorphism
`π₁(K) = F/R → H₁(K)` has the commutator subgroup as its kernel. -/
theorem expVec_mem_range_iff (w : FreeGroup α) :
    Multiplicative.toAdd (expVec w) ∈ LinearMap.range (bdry2 (presComplex ρ)) ↔
      w ∈ relSub ρ ⊔ commutator (FreeGroup α) := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨r, hr, he⟩ := exists_relator_expVec ρ c
    have hk : w * r⁻¹ ∈ (expVec (α := α)).ker := by
      have : expVec (w * r⁻¹) = 1 := by
        rw [map_mul, map_inv]
        have hwr : expVec w = expVec r := by
          apply Multiplicative.toAdd.injective
          rw [he, hc]
        rw [hwr, mul_inv_cancel]
      exact this
    rw [ker_expVec] at hk
    have hw : w = (w * r⁻¹) * r := by group
    rw [hw]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hk) (Subgroup.mem_sup_left hr)
  · intro hw
    have hle : relSub ρ ⊔ commutator (FreeGroup α) ≤ Subgroup.comap expVec (bdrySub ρ) := by
      refine sup_le (relSub_le_comap_bdrySub ρ) ?_
      exact le_trans (Abelianization.commutator_subset_ker expVec) (fun x hx => by
        have : expVec x = 1 := hx
        show expVec x ∈ bdrySub ρ
        rw [this]
        exact Subgroup.one_mem _)
    have h := hle hw
    have h' : expVec w ∈ bdrySub ρ := h
    exact h'

/-! ### The Hurewicz isomorphism -/

/-- The first homology group of the presentation complex: `C₁ = (α →₀ ℤ)` modulo the
boundaries, all one-chains being cycles. -/
abbrev H1pres : Type u := (α →₀ ℤ) ⧸ LinearMap.range (bdry2 (presComplex ρ))

/-- The Hurewicz homomorphism on the free group: a word goes to the class of its exponent-sum
vector. -/
noncomputable def hurFree : FreeGroup α →* Multiplicative (H1pres ρ) :=
  (AddMonoidHom.toMultiplicative
    (LinearMap.range (bdry2 (presComplex ρ))).mkQ.toAddMonoidHom).comp expVec

theorem hurFree_eq_one_iff (w : FreeGroup α) :
    hurFree ρ w = 1 ↔ w ∈ relSub ρ ⊔ commutator (FreeGroup α) := by
  rw [← expVec_mem_range_iff ρ w]
  show (LinearMap.range (bdry2 (presComplex ρ))).mkQ (Multiplicative.toAdd (expVec w)) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

theorem hurFree_surjective : Function.Surjective (hurFree ρ) := by
  intro y
  obtain ⟨c, hc⟩ := (LinearMap.range (bdry2 (presComplex ρ))).mkQ_surjective
    (Multiplicative.toAdd y)
  obtain ⟨w, hw⟩ := expVec_surjective (Multiplicative.ofAdd c)
  refine ⟨w, ?_⟩
  show Multiplicative.ofAdd
    ((LinearMap.range (bdry2 (presComplex ρ))).mkQ (Multiplicative.toAdd (expVec w))) = y
  rw [hw]
  show Multiplicative.ofAdd ((LinearMap.range (bdry2 (presComplex ρ))).mkQ c) = y
  rw [hc]
  rfl

omit [DecidableEq α] in
/-- The commutator subgroup of `G = F/R` is the image of the commutator subgroup of `F`. -/
theorem commutator_presGroup :
    commutator (PresGroup ρ)
      = Subgroup.map (QuotientGroup.mk' (relSub ρ)) (commutator (FreeGroup α)) := by
  have h1 : Subgroup.map (QuotientGroup.mk' (relSub ρ)) (⊤ : Subgroup (FreeGroup α)) = ⊤ :=
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h2 := Subgroup.map_commutator (⊤ : Subgroup (FreeGroup α)) ⊤
    (QuotientGroup.mk' (relSub ρ))
  rw [h1] at h2
  exact h2.symm

omit [DecidableEq α] in
theorem mem_commutator_presGroup_iff (w : FreeGroup α) :
    (QuotientGroup.mk w : PresGroup ρ) ∈ commutator (PresGroup ρ) ↔
      w ∈ relSub ρ ⊔ commutator (FreeGroup α) := by
  rw [commutator_presGroup ρ]
  constructor
  · rintro ⟨c, hc, hceq⟩
    have hmem : c⁻¹ * w ∈ relSub ρ := by
      rw [← QuotientGroup.eq]
      exact hceq
    have hw : w = c * (c⁻¹ * w) := by group
    rw [hw]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hmem)
  · intro hw
    have hle : relSub ρ ⊔ commutator (FreeGroup α) ≤
        Subgroup.comap (QuotientGroup.mk' (relSub ρ))
          (Subgroup.map (QuotientGroup.mk' (relSub ρ)) (commutator (FreeGroup α))) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · have hx1 : (QuotientGroup.mk' (relSub ρ)) x = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact hx
        show (QuotientGroup.mk' (relSub ρ)) x ∈
          Subgroup.map (QuotientGroup.mk' (relSub ρ)) (commutator (FreeGroup α))
        rw [hx1]
        exact Subgroup.one_mem _
      · exact Subgroup.mem_map_of_mem _ hx
    exact hle hw

/-- The Hurewicz homomorphism `π₁(K) = F/R → H₁(K)`. -/
noncomputable def hurPres : PresGroup ρ →* Multiplicative (H1pres ρ) :=
  QuotientGroup.lift (relSub ρ) (hurFree ρ) fun w hw =>
    (hurFree_eq_one_iff ρ w).mpr (Subgroup.mem_sup_left hw)

theorem hurPres_surjective : Function.Surjective (hurPres ρ) := by
  intro y
  obtain ⟨w, hw⟩ := hurFree_surjective ρ y
  exact ⟨QuotientGroup.mk w, hw⟩

/-- **The kernel of the Hurewicz homomorphism is the commutator subgroup.** -/
theorem ker_hurPres : (hurPres ρ).ker = commutator (PresGroup ρ) := by
  ext g
  induction g using QuotientGroup.induction_on with
  | H w =>
      rw [mem_commutator_presGroup_iff ρ w, ← hurFree_eq_one_iff ρ w]
      exact Iff.rfl

/-- **Hurewicz isomorphism in degree one for a presentation complex**: the first homology of
`presComplex ρ` is the abelianization of its fundamental group `G = F/R`. -/
noncomputable def hurewicz1PresEquiv :
    Abelianization (PresGroup ρ) ≃* Multiplicative (H1pres ρ) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_hurPres ρ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (hurPres ρ) (hurPres_surjective ρ))

/-- The same statement with the fundamental group of the complex itself: the abelianization
of `π₁(presComplex ρ)` is the first homology group. -/
noncomputable def hurewicz1Pi1Equiv :
    Abelianization (Pi1 (presComplex ρ) PUnit.unit) ≃* Multiplicative (H1pres ρ) :=
  (MulEquiv.abelianizationCongr (pi1PresEquiv ρ)).trans (hurewicz1PresEquiv ρ)

/-- **Hurewicz in degree one**: the first homology of the presentation complex is the
abelianization of its fundamental group. -/
theorem hurewicz1_pres_abelianization :
    Nonempty (Abelianization (Pi1 (presComplex ρ) PUnit.unit) ≃* Multiplicative (H1pres ρ)) :=
  ⟨hurewicz1Pi1Equiv ρ⟩

end Comb
end FiniteChains
