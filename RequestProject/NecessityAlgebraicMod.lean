import RequestProject.NecessityAlgebraic
import RequestProject.ChainFormulaMod
import RequestProject.FoxCommutatorMod
import RequestProject.FoxRequirementMod

/-!
# Section 2 with the full family of requirements, without any topological interface

`RequestProject/NecessityAlgebraic.lean` derives, from the cell-level data of the chains,
a perfect normal subgroup of `G = π₁(K)` satisfying the *integral* requirements (2.2), and
takes the torsion freeness of `N/[N, N]` as a hypothesis for those subgroups.

Here the same derivation is carried out with the requirements (2.2) of the paper in full —
one for every coefficient vector and every modulus `m` that is `0` or a prime — so that
torsion freeness is only needed for subgroups satisfying the requirements modulo every
prime, which is what the universal coefficient theorem and the Hurewicz dictionary supply
(and what is proved for a presented complex in
`RequestProject/PresentationDictionary.lean`).

The result, `FiniteChains.exists_perfect_normal_foxSatMod`, is the whole of Section 2 with
no reference to any interface for two-complexes: from the cell data of chains of every
length (with the lifting of cycles modulo `m` of Hatcher's book) one gets a perfect normal
subgroup of `G` satisfying all the requirements (2.2).
-/

namespace FiniteChains

open MonoidAlgebra

universe u

variable {G : Type u} [Group G] {I J : Type u}

/-- **Condition (1) at cell level, with the lifting of cycles modulo every `m`.**  For
every `n` the chain `K = X₀ ⊂ ⋯ ⊂ Xₙ` supplies the data of `ChainInput` together with the
property that a cycle which becomes divisible by `m` lifts to a chain divisible by `m`. -/
def HasCellChainsLift (b : I → J → MonoidAlgebra ℤ G) : Prop :=
  ∀ n : ℕ, ∃ (Fund : ℕ → Type u) (_ : ∀ r, Group (Fund r)) (Gen Cell : ℕ → Type u)
    (h : ChainInput b n Fund Gen Cell), ∀ m : ℕ, CycleLiftsMod h m

variable {b : I → J → MonoidAlgebra ℤ G}

/-- The index set of the requirements (2.2): a coefficient vector together with either `0`
(the integral requirement) or a prime `p` (the requirement modulo `p`). -/
abbrev ReqIndex (G : Type u) [Group G] (J : Type u) : Type u :=
  (J →₀ MonoidAlgebra ℤ G) × {m : ℕ // m = 0 ∨ m.Prime}

/-- The requirement attached to an index. -/
def SatIndex (b : I → J → MonoidAlgebra ℤ G) (N : Subgroup G) (vm : ReqIndex G J) : Prop :=
  FoxSatMod vm.2.1 b vm.1 N

/-- **Steps 1–2 of Section 2, with the full family of requirements.**  Any finite family of
requirements is satisfied by a single normal subgroup of `G`. -/
theorem exists_normal_forall_finset_mod (hchains : HasCellChainsLift b)
    (S : Finset (ReqIndex G J)) :
    ∃ N : Subgroup G, N.Normal ∧ ∀ vm ∈ S, SatIndex b N vm := by
  classical
  obtain ⟨Fund, inst, Gen, Cell, h, hlift⟩ := hchains S.card
  letI := inst
  obtain ⟨r, -, hr⟩ :=
    exists_stage_satisfying_all S le_rfl (fun r vm => SatIndex b (h.phi r).ker vm)
      (fun r vm hv s hrs hsn =>
        h.foxSatMod_of_not_foxSatMod vm.2.1 (hlift vm.2.1) vm.1 r hv s hrs hsn)
  exact ⟨(h.phi r).ker, inferInstance, hr⟩

/-- **The conclusion of Section 2, with the full family of requirements.**  From the cell
data of chains of every length one obtains a perfect normal subgroup of `G` satisfying all
the requirements (2.2), integrally and modulo every prime.  The only hypothesis besides the
chains is the torsion freeness of `N/[N, N]` for subgroups satisfying the requirements
modulo every prime — the universal-coefficient/Hurewicz input of Section 2. -/
theorem exists_perfect_normal_foxSatMod (hchains : HasCellChainsLift b)
    (hfin : ∀ v : J →₀ MonoidAlgebra ℤ G, {i : I | foxBoundary b v i ≠ 0}.Finite)
    (hcol : ∀ j, {i : I | b i j ≠ 0}.Finite)
    (htf : ∀ (N : Subgroup G) [N.Normal],
      (∀ p : ℕ, p.Prime → ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod p b v N) →
        IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆))) :
    ∃ N : Subgroup G, N.Normal ∧
      (∀ p : ℕ, p.Prime → ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod p b v N) ∧
      (∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v N) ∧ ⁅N, N⁆ = N := by
  classical
  have hdet : FinitelyDetermined (SatIndex b) := fun vm =>
    foxSatMod_finitelyDetermined vm.2.1 b vm.1 (hfin vm.1)
  -- compactness
  obtain ⟨M, hMnormal, hM⟩ :=
    exists_normal_subgroup_forall (SatIndex b) hdet (exists_normal_forall_finset_mod hchains)
  -- a minimal normal subgroup satisfying all the requirements
  obtain ⟨N, -, hNnormal, hN, hNmin⟩ :=
    exists_minimal_normal_sat (fun N => ∀ vm : ReqIndex G J, SatIndex b N vm)
      (fun C hchain hne hC =>
        sat_sInf_of_finitelyDetermined (SatIndex b) hdet hchain hne
          (fun N hNmem => (hC N hNmem).2))
      M hMnormal hM
  haveI := hNnormal
  have hmod : ∀ p : ℕ, p.Prime → ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod p b v N :=
    fun p hp v => hN (v, ⟨p, Or.inr hp⟩)
  have hint : ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v N :=
    fun v => (foxSatMod_zero_iff b v N).1 (hN (v, ⟨0, Or.inl rfl⟩))
  haveI := htf N hmod
  -- Lemma 2.1: the requirements pass to the commutator subgroup
  have hsatcomm : ∀ vm : ReqIndex G J, SatIndex b ⁅N, N⁆ vm := by
    rintro ⟨v, m, hm⟩
    rcases hm with rfl | hp
    · exact (foxSatMod_zero_iff b v ⁅N, N⁆).2 (foxSat_commutator b hcol N hint v)
    · haveI := Fact.mk hp
      exact foxSatMod_commutator m b hcol N (fun w => hmod m hp w) v
  have hcomm : (⁅N, N⁆ : Subgroup G).Normal := inferInstance
  exact ⟨N, hNnormal, hmod, hint,
    hNmin ⁅N, N⁆ (Subgroup.commutator_le_left N N) hcomm hsatcomm⟩

end FiniteChains
