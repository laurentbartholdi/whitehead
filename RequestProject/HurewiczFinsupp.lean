import RequestProject.CrowellFinsupp
import RequestProject.UniversalCoefficients

/-! Integral first homology and its torsion test for arbitrarily many cells. -/

namespace FiniteChains

variable {α J : Type*} [DecidableEq α]
  (N : Subgroup (FreeGroup α)) [N.Normal] (ρ : J → FreeGroup α)

noncomputable def fsCoverCycles : AddSubgroup (α →₀ CoverRing N) :=
  (coverFirstBoundary N).toAddMonoidHom.ker

noncomputable def fsCoverBoundaries : AddSubgroup (α →₀ CoverRing N) :=
  (coverSecondBoundary N ρ).toAddMonoidHom.range

def FSCoverH1 :=
  fsCoverCycles N ⧸ (fsCoverBoundaries N ρ).addSubgroupOf (fsCoverCycles N)

noncomputable instance fsCoverH1_addCommGroup : AddCommGroup (FSCoverH1 N ρ) :=
  inferInstanceAs (AddCommGroup
    (fsCoverCycles N ⧸ (fsCoverBoundaries N ρ).addSubgroupOf (fsCoverCycles N)))

noncomputable def fsFoxCycle (w : N) : fsCoverCycles N :=
  ⟨coverFoxGradient N (w : FreeGroup α), coverFoxGradient_isCycle N w.property⟩

noncomputable def fsFoxH1Hom : N →* Multiplicative (FSCoverH1 N ρ) where
  toFun w := Multiplicative.ofAdd (QuotientAddGroup.mk (fsFoxCycle N w))
  map_one' := by
    have h : fsFoxCycle N (1 : N) = 0 := Subtype.ext (coverFoxGradient_one N)
    change Multiplicative.ofAdd (QuotientAddGroup.mk (fsFoxCycle N 1)) = 1
    rw [h]
    rfl
  map_mul' v w := by
    have h : fsFoxCycle N (v * w) = fsFoxCycle N v + fsFoxCycle N w :=
      Subtype.ext (coverFoxGradient_mul N v.property (w : FreeGroup α))
    change Multiplicative.ofAdd (QuotientAddGroup.mk (fsFoxCycle N (v * w))) = _
    rw [h]
    rfl

theorem fsFoxH1Hom_surjective : Function.Surjective (fsFoxH1Hom N ρ) := by
  intro z
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd z)
  obtain ⟨w, hw, he⟩ := exists_mem_of_coverFirstBoundary_eq_zero N c.val c.property
  refine ⟨⟨w, hw⟩, ?_⟩
  have h : fsFoxCycle N ⟨w, hw⟩ = c := Subtype.ext he.symm
  change Multiplicative.ofAdd (QuotientAddGroup.mk (fsFoxCycle N ⟨w, hw⟩)) = z
  rw [h, hc]
  rfl

theorem fsFoxH1Hom_ker (hρ : ∀ j, ρ j ∈ N) :
    (fsFoxH1Hom N ρ).ker =
      (Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆).subgroupOf N := by
  ext w
  constructor
  · intro hw
    have hz : QuotientAddGroup.mk
        (s := (fsCoverBoundaries N ρ).addSubgroupOf (fsCoverCycles N))
        (fsFoxCycle N w) = 0 := hw
    obtain ⟨c, hc⟩ := (QuotientAddGroup.eq_zero_iff _).mp hz
    exact (coverFoxGradient_mem_range_iff N ρ hρ w.property).mp ⟨c, hc⟩
  · intro hw
    obtain ⟨c, hc⟩ := (coverFoxGradient_mem_range_iff N ρ hρ w.property).mpr hw
    have hz : QuotientAddGroup.mk
        (s := (fsCoverBoundaries N ρ).addSubgroupOf (fsCoverCycles N))
        (fsFoxCycle N w) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr ⟨c, hc⟩
    change Multiplicative.ofAdd (QuotientAddGroup.mk (fsFoxCycle N w)) = 1
    rw [hz]
    rfl

/-- The Hurewicz dictionary `H₁ = Ñ/(R [Ñ,Ñ])`, using finite chains and no finite-type
assumptions on either the generator set or the relator set. -/
noncomputable def fsCoverH1Equiv (hρ : ∀ j, ρ j ∈ N) :
    (N ⧸ (Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆).subgroupOf N) ≃*
      Multiplicative (FSCoverH1 N ρ) :=
  (QuotientGroup.quotientMulEquivOfEq (fsFoxH1Hom_ker N ρ hρ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (fsFoxH1Hom N ρ) (fsFoxH1Hom_surjective N ρ))

/-- The prime-by-prime lifting condition excludes torsion in the covering subgroup's
abelianization, with arbitrary cell-index sets. -/
theorem fs_mem_relComm_of_pow_mem (hρ : ∀ j, ρ j ∈ N)
    (hmod : ∀ p : ℕ, p.Prime →
      LiftsMod (coverSecondBoundary N ρ).toAddMonoidHom p)
    {w : FreeGroup α} (hw : w ∈ N) {n : ℕ} (hn : n ≠ 0)
    (hpow : w ^ n ∈ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆) :
    w ∈ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆ := by
  have he : coverFoxGradient N (w ^ n) = n • coverFoxGradient N w := by
    simpa using coverFoxGradient_zpow N hw (n : ℤ)
  obtain ⟨c, hc⟩ := (coverFoxGradient_mem_range_iff N ρ hρ (N.pow_mem hw n)).mpr hpow
  have hr : n • coverFoxGradient N w ∈ (coverSecondBoundary N ρ).toAddMonoidHom.range :=
    ⟨c, hc.trans he⟩
  have hmem := mem_range_of_nsmul_mem_range (coverSecondBoundary N ρ).toAddMonoidHom
    hmod n hn (coverFoxGradient N w) hr
  exact (coverFoxGradient_mem_range_iff N ρ hρ hw).mp hmem

end FiniteChains
