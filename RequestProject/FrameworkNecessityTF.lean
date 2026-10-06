module

public import RequestProject.FrameworkNecessityMod

@[expose] public section

/-!
# `(1) ⇒ (2)` with the Hurewicz input in the form "torsion freeness of `N/[N, N]`"

`RequestProject/FrameworkNecessityMod.lean` assembles the implication `(1) ⇒ (2)` from three
inputs: the cell data of the chains, the construction of the cover, and the Hurewicz
dictionary in the form of an injective map `N/[N, N] → coker ∂_{2,N}`.

The dictionary is used there for one purpose only: to know that `N/[N, N]` is torsion free.
This file records the same assembly with that consequence as the hypothesis, so that it can
be discharged directly (which is done, for a presented complex, in
`RequestProject/PresentationDictionary.lean`).
-/

namespace FiniteChains

open MonoidAlgebra

universe u

variable {W : TwoComplexData.{u}} {K : W.Cx}

set_option maxHeartbeats 1000000 in
/-- **`NecessityInputs` from the cell-level data of the chains**, with the Hurewicz input in
the form "`N/[N, N]` is torsion free for every normal subgroup satisfying the requirements
modulo every prime". -/
noncomputable def necessityInputs_of_cellDataMod_tf {G : Type u} [inst : Group G] {I J : Type u}
    (b : I → J → MonoidAlgebra ℤ G)
    (hfin : ∀ v : J →₀ MonoidAlgebra ℤ G, {i : I | foxBoundary b v i ≠ 0}.Finite)
    (hcol : ∀ j, {i : I | b i j ≠ 0}.Finite)
    (cellData : ∀ (c : ℕ → W.Cx) (n : ℕ), c 0 = K → IsZeroChain W c n →
      ∃ (Fund : ℕ → Type u) (_ : ∀ r, Group (Fund r)) (Gen Cell : ℕ → Type u)
        (h : ChainInput b n Fund Gen Cell), ∀ m : ℕ, CycleLiftsMod h m)
    (htf : ∀ (N : Subgroup G) [N.Normal],
      (∀ p : ℕ, p.Prime → ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod p b v N) →
        IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆)))
    (cover : ∀ N : Subgroup G, N.Normal → (∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v N) →
      ⁅N, N⁆ = N → HasAcyclicRegularCover W K) :
    NecessityInputs W K where
  G := G
  grp := inst
  Req := ReqMod G J
  Sat := fun N vm => FoxSatMod vm.2.1 b vm.1 N
  chain_subgroups := by
    intro c n hc0 hc
    obtain ⟨Fund, instF, Gen, Cell, h, hlift⟩ := cellData c n hc0 hc
    letI := instF
    exact ⟨fun r => (h.phi r).ker, fun r => inferInstance,
      fun r vm hv s hrs hsn =>
        h.foxSatMod_of_not_foxSatMod vm.2.1 (hlift vm.2.1) vm.1 r hv s hrs hsn⟩
  det := fun vm => foxSatMod_finitelyDetermined vm.2.1 b vm.1 (hfin vm.1)
  sat_sInf_chain := fun C hchain hne hC =>
    sat_sInf_of_finitelyDetermined
      (fun (N : Subgroup G) (vm : ReqMod G J) => FoxSatMod vm.2.1 b vm.1 N)
      (fun (vm : ReqMod G J) => foxSatMod_finitelyDetermined vm.2.1 b vm.1 (hfin vm.1))
      hchain hne
      (fun N hNmem => (hC N hNmem).2)
  sat_commutator := by
    intro N hN hsat
    haveI := hN
    haveI : IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆)) :=
      htf N (fun p hp v => hsat (v, ⟨p, Or.inr hp⟩))
    rintro ⟨v, m, hm⟩
    rcases hm with rfl | hp
    · exact (foxSatMod_zero_iff b v ⁅N, N⁆).2
        (foxSat_commutator b hcol N
          (fun w => (foxSatMod_zero_iff b w N).1 (hsat (w, ⟨0, Or.inl rfl⟩))) v)
    · haveI := Fact.mk hp
      exact foxSatMod_commutator m b hcol N (fun w => hsat (w, ⟨m, Or.inr hp⟩)) v
  cover_of_perfect := fun N hN hsat hperf =>
    cover N hN (fun v => (foxSatMod_zero_iff b v N).1 (hsat (v, ⟨0, Or.inl rfl⟩))) hperf

/-- **`(1) ⇒ (2)` of Theorem A** with the Hurewicz input in the form "`N/[N, N]` is torsion
free". -/
theorem hasAcyclicRegularCover_of_cellDataMod_tf {G : Type u} [Group G] {I J : Type u}
    (b : I → J → MonoidAlgebra ℤ G)
    (hfin : ∀ v : J →₀ MonoidAlgebra ℤ G, {i : I | foxBoundary b v i ≠ 0}.Finite)
    (hcol : ∀ j, {i : I | b i j ≠ 0}.Finite)
    (cellData : ∀ (c : ℕ → W.Cx) (n : ℕ), c 0 = K → IsZeroChain W c n →
      ∃ (Fund : ℕ → Type u) (_ : ∀ r, Group (Fund r)) (Gen Cell : ℕ → Type u)
        (h : ChainInput b n Fund Gen Cell), ∀ m : ℕ, CycleLiftsMod h m)
    (htf : ∀ (N : Subgroup G) [N.Normal],
      (∀ p : ℕ, p.Prime → ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod p b v N) →
        IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆)))
    (cover : ∀ N : Subgroup G, N.Normal → (∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v N) →
      ⁅N, N⁆ = N → HasAcyclicRegularCover W K)
    (h : HasZeroChains W K) : HasAcyclicRegularCover W K :=
  hasAcyclicRegularCover_of_hasZeroChains
    (necessityInputs_of_cellDataMod_tf b hfin hcol cellData htf cover) h

end FiniteChains
