import RequestProject.HurewiczDictionary
import RequestProject.PresentationDictionary

/-!
# The Hurewicz dictionary as an explicit isomorphism `H₁(K_N) ≅ N/[N, N]`

`RequestProject/HurewiczDictionary.lean` proves the two membership statements that identify
the first homology of the cover.  Here they are assembled into honest isomorphisms of
groups.

For a presentation `⟨x | ρ⟩` with free group `F`, relator subgroup `R = ⟪ρ⟫`, a normal
subgroup `Ñ ◁ F` containing the relators and cover group `Q = F/Ñ`:

* `FiniteChains.CoverH1` is the first homology `ker ∂₁ / im ∂₂` of the chain complex of the
  cover `K_N`;
* `FiniteChains.coverH1Equiv : (Ñ ⧸ (R·[Ñ, Ñ])) ≃* Multiplicative (H₁(K_N))` — the Crowell
  sequence (surjectivity) plus the Magnus theorem (the kernel);
* `FiniteChains.quotRelCommEquivAbelianization : (Ñ ⧸ (R·[Ñ, Ñ])) ≃* Abelianization N`,
  where `N = Ñ/R ◁ G = F/R`;
* `FiniteChains.coverH1EquivAbelianization : Abelianization N ≃* Multiplicative (H₁(K_N))`,
  the Hurewicz dictionary `H₁(K_N) = N/[N, N]` of Section 2.
-/

namespace FiniteChains

open MonoidAlgebra

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (Nsub : Subgroup (FreeGroup α)) [Nsub.Normal]
variable {J : Type*} [Fintype J] (ρ : J → FreeGroup α)

/-! ### The homology of the chain complex of the cover -/

/-- The first boundary `∂₁` of the cover as a homomorphism of additive groups. -/
noncomputable def bdry1Hom : (α → CoverRing Nsub) →+ CoverRing Nsub where
  toFun := bdry1 Nsub
  map_zero' := by simp [bdry1]
  map_add' := bdry1_add Nsub

/-- The cycles `ker ∂₁` of the chain complex of the cover. -/
noncomputable def coverCycles : AddSubgroup (α → CoverRing Nsub) := (bdry1Hom Nsub).ker

/-- The boundaries `im ∂₂` of the chain complex of the cover. -/
noncomputable def coverBdrys : AddSubgroup (α → CoverRing Nsub) := (bdry2Hom Nsub ρ).range

omit [DecidableEq α] in
theorem mem_coverCycles_iff (c : α → CoverRing Nsub) :
    c ∈ coverCycles Nsub ↔ bdry1 Nsub c = 0 := Iff.rfl

omit [Fintype α] in
theorem mem_coverBdrys_iff (c : α → CoverRing Nsub) :
    c ∈ coverBdrys Nsub ρ ↔ ∃ u : J → CoverRing Nsub, bdry2 Nsub ρ u = c := Iff.rfl

/-- The boundaries are cycles: `∂₁ ∘ ∂₂ = 0`. -/
theorem coverBdrys_le_coverCycles (hρ : ∀ j, ρ j ∈ Nsub) :
    coverBdrys Nsub ρ ≤ coverCycles Nsub := by
  rintro c ⟨u, rfl⟩
  exact bdry1_bdry2 Nsub ρ hρ u

/-- The first homology `H₁(K_N) = ker ∂₁ / im ∂₂` of the chain complex of the cover. -/
noncomputable abbrev CoverH1 : Type _ :=
  coverCycles Nsub ⧸ (coverBdrys Nsub ρ).addSubgroupOf (coverCycles Nsub)

/-- The cycle determined by an element of `Ñ`. -/
noncomputable def foxCycle (w : Nsub) : coverCycles Nsub :=
  ⟨foxVec Nsub (w : FreeGroup α), bdry1_foxVec Nsub w.2⟩

/-- The Hurewicz map `Ñ → H₁(K_N)`, `w ↦ [Fox vector of w]`. -/
noncomputable def foxH1Hom : Nsub →* Multiplicative (CoverH1 Nsub ρ) where
  toFun w := Multiplicative.ofAdd (QuotientAddGroup.mk (foxCycle Nsub w))
  map_one' := by
    show Multiplicative.ofAdd (QuotientAddGroup.mk (foxCycle Nsub 1)) = 1
    have h : foxCycle Nsub (1 : Nsub) = 0 := by
      apply Subtype.ext
      show foxVec Nsub (1 : FreeGroup α) = 0
      simp
    rw [h]
    rfl
  map_mul' v w := by
    have h : foxCycle Nsub (v * w) = foxCycle Nsub v + foxCycle Nsub w := by
      apply Subtype.ext
      exact foxVec_mul v.2 (w : FreeGroup α)
    show Multiplicative.ofAdd (QuotientAddGroup.mk (foxCycle Nsub (v * w))) = _
    rw [h]
    rfl

theorem foxH1Hom_surjective : Function.Surjective (foxH1Hom Nsub ρ) := by
  intro z
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd z)
  obtain ⟨w, hw, hwc⟩ := exists_mem_of_bdry1_eq_zero Nsub (c : α → CoverRing Nsub) c.2
  refine ⟨⟨w, hw⟩, ?_⟩
  show Multiplicative.ofAdd (QuotientAddGroup.mk (foxCycle Nsub ⟨w, hw⟩)) = z
  have h : foxCycle Nsub ⟨w, hw⟩ = c := Subtype.ext hwc.symm
  rw [h, hc]
  rfl

theorem foxH1Hom_ker (hρ : ∀ j, ρ j ∈ Nsub) :
    (foxH1Hom Nsub ρ).ker = (relComm Nsub ρ).subgroupOf Nsub := by
  ext w
  constructor
  · intro hw
    have hmem : foxCycle Nsub w ∈ (coverBdrys Nsub ρ).addSubgroupOf (coverCycles Nsub) := by
      have h0 : QuotientAddGroup.mk (s := (coverBdrys Nsub ρ).addSubgroupOf (coverCycles Nsub))
          (foxCycle Nsub w) = 0 := hw
      exact (QuotientAddGroup.eq_zero_iff _).1 h0
    obtain ⟨u, hu⟩ := hmem
    exact (foxVec_mem_range_bdry2_iff Nsub ρ hρ w.2).1 ⟨u, hu⟩
  · intro hw
    obtain ⟨u, hu⟩ := (foxVec_mem_range_bdry2_iff Nsub ρ hρ w.2).2 hw
    show Multiplicative.ofAdd (QuotientAddGroup.mk (foxCycle Nsub w)) = 1
    have h0 : QuotientAddGroup.mk (s := (coverBdrys Nsub ρ).addSubgroupOf (coverCycles Nsub))
        (foxCycle Nsub w) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).2 ⟨u, hu⟩
    rw [h0]
    rfl

instance relComm_normal : (relComm Nsub ρ).Normal := by
  rw [relComm]
  infer_instance

/-- **The Hurewicz dictionary, first half**: the first homology of the chain complex of the
cover is `Ñ/(R·[Ñ, Ñ])`. -/
noncomputable def coverH1Equiv (hρ : ∀ j, ρ j ∈ Nsub) :
    (Nsub ⧸ (relComm Nsub ρ).subgroupOf Nsub) ≃* Multiplicative (CoverH1 Nsub ρ) :=
  (QuotientGroup.quotientMulEquivOfEq (foxH1Hom_ker Nsub ρ hρ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (foxH1Hom_surjective Nsub ρ))

/-- The isomorphism is induced by the Hurewicz map: the class of `w ∈ Ñ` goes to the class
of the Fox vector of `w`. -/
theorem coverH1Equiv_mk (hρ : ∀ j, ρ j ∈ Nsub) (w : Nsub) :
    coverH1Equiv Nsub ρ hρ (QuotientGroup.mk w) = foxH1Hom Nsub ρ w := rfl

/-! ### `Ñ/(R·[Ñ, Ñ]) = N/[N, N]` -/

/-- The map `Ñ → N = Ñ/R`. -/
noncomputable def toPresN : Nsub →* presSub ρ Nsub :=
  MonoidHom.codRestrict ((QuotientGroup.mk' (relSub ρ)).comp Nsub.subtype) (presSub ρ Nsub)
    (fun w => ⟨w, w.2, rfl⟩)

omit [Fintype α] [DecidableEq α] [Fintype J] [Nsub.Normal] in
theorem toPresN_surjective : Function.Surjective (toPresN Nsub ρ) := by
  rintro ⟨_, w, hw, rfl⟩
  exact ⟨⟨w, hw⟩, rfl⟩

/-- The composite `Ñ → N → N/[N, N]`. -/
noncomputable def abelPresHom : Nsub →* Abelianization (presSub ρ Nsub) :=
  (Abelianization.of).comp (toPresN Nsub ρ)

omit [Fintype α] [DecidableEq α] [Fintype J] [Nsub.Normal] in
theorem abelPresHom_surjective : Function.Surjective (abelPresHom Nsub ρ) := by
  intro z
  refine QuotientGroup.induction_on z fun y => ?_
  obtain ⟨w, rfl⟩ := toPresN_surjective Nsub ρ y
  exact ⟨w, rfl⟩

omit [Fintype α] [DecidableEq α] [Fintype J] [Nsub.Normal] in
theorem abelPresHom_ker : (abelPresHom Nsub ρ).ker = (relComm Nsub ρ).subgroupOf Nsub := by
  have hcomm : ⁅presSub ρ Nsub, presSub ρ Nsub⁆
      = ⁅Nsub, Nsub⁆.map (QuotientGroup.mk' (relSub ρ)) := by
    rw [presSub, ← Subgroup.map_commutator]
  ext w
  have hmem : w ∈ (abelPresHom Nsub ρ).ker ↔
      toPresN Nsub ρ w ∈ (Abelianization.of).ker := Iff.rfl
  have hsub : ∀ x : presSub ρ Nsub, x ∈ commutator (presSub ρ Nsub) ↔
      (x : PresGroup ρ) ∈ ⁅presSub ρ Nsub, presSub ρ Nsub⁆ := by
    intro x
    rw [← Subgroup.map_subtype_commutator]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      exact (Subtype.ext hxy : y = x) ▸ hy
  have hval : ((toPresN Nsub ρ w : presSub ρ Nsub) : PresGroup ρ)
      = (QuotientGroup.mk' (relSub ρ)) (w : FreeGroup α) := rfl
  rw [hmem, Abelianization.ker_of, hsub, hcomm, hval, ← Subgroup.mem_comap,
    Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf, relComm, sup_comm]
  exact Iff.rfl

/-- The quotient `Ñ/(R·[Ñ, Ñ])` is the abelianization of `N = Ñ/R`. -/
noncomputable def quotRelCommEquivAbelianization :
    (Nsub ⧸ (relComm Nsub ρ).subgroupOf Nsub) ≃* Abelianization (presSub ρ Nsub) :=
  (QuotientGroup.quotientMulEquivOfEq (abelPresHom_ker Nsub ρ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (abelPresHom_surjective Nsub ρ))

/-- **The Hurewicz dictionary `H₁(K_N) = N/[N, N]`** as an isomorphism of groups. -/
noncomputable def coverH1EquivAbelianization (hρ : ∀ j, ρ j ∈ Nsub) :
    Abelianization (presSub ρ Nsub) ≃* Multiplicative (CoverH1 Nsub ρ) :=
  (quotRelCommEquivAbelianization Nsub ρ).symm.trans (coverH1Equiv Nsub ρ hρ)

end FiniteChains
