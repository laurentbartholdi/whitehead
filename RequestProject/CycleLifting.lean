import RequestProject.CoverAcyclic
import RequestProject.HurewiczDictionary
import RequestProject.HurewiczIso
import RequestProject.PresentationDictionary

/-!
# Cycles lift modulo `m`: a theorem, not a citation

Formula (2.3) modulo `m` was derived in `RequestProject/ChainFormulaMod.lean` from the
property `CycleLiftsMod`, quoted in the paper from Hatcher: in the chain complex of the
universal cover of a stage, a chain whose boundary is divisible by `m` is congruent modulo
`m` to a genuine cycle.

For the two-complex of a finite presentation this is a consequence of what is already
proved here.  Write `C₂ --∂₂--> C₁ --∂₁--> C₀` for the chain complex of the universal cover
(the cover attached to the relator subgroup `R`, with deck group `G = π₁(K)`).  Then
`H₁ = 0` (`FiniteChains.exists_bdry2_preimage`, which for `Ñ = R` needs no hypothesis).
If `∂₂u = m·w` then `m·∂₁w = ∂₁∂₂u = 0`, so `∂₁w = 0` because the group ring is torsion
free, hence `w = ∂₂z` and `u - m·z` is a cycle congruent to `u` modulo `m`.

`FiniteChains.exists_cycle_of_bdry2_nsmul` is this statement in the coordinates used by
`ChainInput`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

variable {β : Type*} [Fintype β] [DecidableEq β]
variable {K : Type*} [Fintype K] [DecidableEq K] (σ : K → FreeGroup β)

omit [Fintype β] [DecidableEq β] [Fintype K] [DecidableEq K] in
/-- The relators lie in the relator subgroup. -/
theorem rel_mem_relSub' (j : K) : σ j ∈ relSub σ :=
  Subgroup.subset_normalClosure (Set.mem_range_self j)

omit [Fintype β] [DecidableEq β] [Fintype K] [DecidableEq K] in
/-- A group ring over `ℤ` has no additive torsion. -/
theorem nsmul_eq_zero_iff_of_ne {G : Type*} (m : ℕ) (hm : m ≠ 0) (x : MonoidAlgebra ℤ G) :
    m • x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply MonoidAlgebra.coeff_injective
    refine Finsupp.ext fun g => ?_
    have hg : m • x.coeff g = 0 := by
      have := congrArg (fun y : MonoidAlgebra ℤ G => y.coeff g) h
      simpa only [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_zero, Finsupp.zero_apply] using this
    have : (m : ℤ) * x.coeff g = 0 := by
      rw [← nsmul_eq_mul]
      exact hg
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd (Nat.cast_eq_zero.1 h') hm
    · simpa using h'
  · rintro rfl
    simp

omit [Fintype β] [DecidableEq K] in
/-- The sum over the support is the sum over all two-cells. -/
theorem sum_support_eq_sum_univ (u : K →₀ MonoidAlgebra ℤ (PresGroup σ)) (a : β) :
    ∑ c ∈ u.support, u c * foxMatrixPres σ a c
      = ∑ c : K, u c * foxMatrixPres σ a c := by
  classical
  refine Finset.sum_subset (Finset.subset_univ _) fun c _ hc => ?_
  have : u c = 0 := by simpa using hc
  rw [this, zero_mul]

omit [Fintype β] [DecidableEq K] in
/-- In the coordinates of the boundary of the universal cover. -/
theorem bdry2_eq_sum (v : K → MonoidAlgebra ℤ (PresGroup σ)) :
    bdry2 (relSub σ) σ v = fun a => ∑ c : K, v c * foxMatrixPres σ a c := by
  funext a
  rw [bdry2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [foxMatrixPres, proj_eq_quotRingHom]

omit [DecidableEq K] in
/-- **Cycles lift modulo `m`.**  If the boundary of a two-chain of the universal cover is
divisible by `m`, then the chain is congruent modulo `m` to a cycle. -/
theorem exists_cycle_of_bdry2_nsmul (m : ℕ) (u : K →₀ MonoidAlgebra ℤ (PresGroup σ))
    (hu : ∀ a : β, ∃ w, ∑ c ∈ u.support, u c * foxMatrixPres σ a c = m • w) :
    ∃ u' : K →₀ MonoidAlgebra ℤ (PresGroup σ),
      (∀ a : β, ∑ c ∈ u'.support, u' c * foxMatrixPres σ a c = 0) ∧
        ∃ z : K →₀ MonoidAlgebra ℤ (PresGroup σ), u = u' + m • z := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · -- for `m = 0` the hypothesis already says that `u` is a cycle
    refine ⟨u, fun a => ?_, 0, by simp⟩
    obtain ⟨w, hw⟩ := hu a
    simpa using hw
  have hm : m ≠ 0 := hmpos.ne'
  choose w hw using hu
  set uf : K → CoverRing (relSub σ) := fun c => u c with huf
  have hbdry : bdry2 (relSub σ) σ uf = fun a => m • w a := by
    rw [bdry2_eq_sum]
    funext a
    rw [← sum_support_eq_sum_univ σ u a, hw a]
  -- the vector `w` is a one-dimensional cycle
  have hzero : bdry1 (relSub σ) (bdry2 (relSub σ) σ uf) = 0 :=
    bdry1_bdry2 (relSub σ) σ (rel_mem_relSub' σ) uf
  have hw1 : bdry1 (relSub σ) w = 0 := by
    rw [hbdry, show (fun a => m • w a) = m • w from rfl,
      show bdry1 (relSub σ) (m • w) = m • bdry1 (relSub σ) w from
        map_nsmul (bdry1Hom (relSub σ)) m w] at hzero
    exact (nsmul_eq_zero_iff_of_ne m hm _).1 hzero
  -- `H₁ = 0` for the universal cover
  obtain ⟨z, hz⟩ :=
    exists_bdry2_preimage (relSub σ) σ (rel_mem_relSub' σ) le_sup_left w hw1
  set zF : K →₀ MonoidAlgebra ℤ (PresGroup σ) := Finsupp.equivFunOnFinite.symm z with hzF
  refine ⟨u - m • zF, fun a => ?_, zF, by abel⟩
  have hcoef : ∀ c : K, (u - m • zF) c = uf c - m • z c := by
    intro c
    simp [hzF, huf]
  have hsub : bdry2 (relSub σ) σ (uf - m • z)
      = bdry2 (relSub σ) σ uf - m • bdry2 (relSub σ) σ z := by
    have h1 : (bdry2Hom (relSub σ) σ) (uf - m • z)
        = (bdry2Hom (relSub σ) σ) uf - (bdry2Hom (relSub σ) σ) (m • z) := map_sub _ _ _
    rw [show (bdry2Hom (relSub σ) σ) (m • z) = m • bdry2 (relSub σ) σ z from
      map_nsmul (bdry2Hom (relSub σ) σ) m z] at h1
    exact h1
  calc ∑ c ∈ (u - m • zF).support, (u - m • zF) c * foxMatrixPres σ a c
      = ∑ c : K, (u - m • zF) c * foxMatrixPres σ a c :=
        sum_support_eq_sum_univ σ (u - m • zF) a
    _ = ∑ c : K, (uf - m • z) c * foxMatrixPres σ a c := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hcoef c]
        rfl
    _ = bdry2 (relSub σ) σ (uf - m • z) a := (congrFun (bdry2_eq_sum σ (uf - m • z)) a).symm
    _ = 0 := by
        rw [hsub, hbdry, hz]
        show m • w a - (m • w) a = 0
        simp

end FiniteChains
