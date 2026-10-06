module

public import RequestProject.FrameworkNecessity
public import RequestProject.ChainFormulaMod
public import RequestProject.FoxCommutatorMod

@[expose] public section

/-!
# `(1) ⇒ (2)` with the full family of requirements (2.2)

`RequestProject/FrameworkNecessity.lean` assembles the implication `(1) ⇒ (2)` of Theorem A
using the integral requirements (2.2) only, and quotes the torsion freeness of `N/[N, N]`
(the universal-coefficient input) as a hypothesis.

Here the same assembly is carried out with the requirements (2.2) of the paper in full:
one requirement for each coefficient vector `v` and each `m` that is either `0` (the
integral requirement) or a prime (the requirement modulo `p`).  All of Section 2 is then
supplied by theorems of this development:

* formula (2.3) modulo `m` — `ChainInput.foxSatMod_of_not_foxSatMod`;
* finite determinacy — `foxSatMod_finitelyDetermined`;
* the intersection step — `sat_sInf_of_finitelyDetermined`;
* Lemma 2.1, integrally and modulo `p` — `foxSat_commutator` and `foxSatMod_commutator`;
* **the universal-coefficient input is now a theorem**: the requirements modulo every prime
  force the cokernel of the Fox boundary to be torsion free
  (`foxCokernel_torsionFree_of_foxSatMod`), so torsion freeness of `N/[N, N]` follows from
  the Hurewicz dictionary alone.

Three topological inputs remain, all of them cell-level statements about the chain:

* `cellData` — a chain of two-complexes gives the cell data `ChainInput` together with the
  lifting of cycles modulo `m` (`CycleLiftsMod`);
* `dict` — the Hurewicz dictionary: `N/[N, N] = H₁(K_N)` embeds in the cokernel of the Fox
  boundary;
* `cover` — a perfect normal subgroup satisfying the requirements yields the acyclic
  regular cover.
-/

namespace FiniteChains

open MonoidAlgebra

universe u

variable {W : TwoComplexData.{u}} {K : W.Cx}

/-- The index of the requirements (2.2): a coefficient vector together with either `0`
(the integral requirement) or a prime `p` (the requirement modulo `p`). -/
abbrev ReqMod (G : Type u) [Group G] (J : Type u) : Type u :=
  (J →₀ MonoidAlgebra ℤ G) × {m : ℕ // m = 0 ∨ m.Prime}

set_option maxHeartbeats 1000000 in
/-- **`NecessityInputs` from the cell-level data of the chains, with the requirements
(2.2) in full.** -/
noncomputable def necessityInputs_of_cellDataMod {G : Type u} [inst : Group G] {I J : Type u}
    (b : I → J → MonoidAlgebra ℤ G)
    (hfin : ∀ v : J →₀ MonoidAlgebra ℤ G, {i : I | foxBoundary b v i ≠ 0}.Finite)
    (hcol : ∀ j, {i : I | b i j ≠ 0}.Finite)
    (cellData : ∀ (c : ℕ → W.Cx) (n : ℕ), c 0 = K → IsZeroChain W c n →
      ∃ (Fund : ℕ → Type u) (_ : ∀ r, Group (Fund r)) (Gen Cell : ℕ → Type u)
        (h : ChainInput b n Fund Gen Cell), ∀ m : ℕ, CycleLiftsMod h m)
    (dict : ∀ (N : Subgroup G) [N.Normal],
      ∃ f : (N.map (QuotientGroup.mk' ⁅N, N⁆)) →* Multiplicative (foxCokernel b hcol N),
        Function.Injective f)
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
    -- the universal-coefficient input, now a theorem
    haveI : IsAddTorsionFree (foxCokernel b hcol N) :=
      foxCokernel_torsionFree_of_foxSatMod b hcol N
        (fun p hp v => hsat (v, ⟨p, Or.inr hp⟩))
    haveI : IsMulTorsionFree (Multiplicative (foxCokernel b hcol N)) :=
      isMulTorsionFree_multiplicative
    obtain ⟨f, hf⟩ := dict N
    have hfi : ∀ a c : (N.map (QuotientGroup.mk' ⁅N, N⁆)), f a = f c → a = c :=
      fun a c hac => hf hac
    haveI : IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆)) :=
      isMulTorsionFree_of_injective (A := Multiplicative (foxCokernel b hcol N)) f hfi
    rintro ⟨v, m, hm⟩
    rcases hm with rfl | hp
    · exact (foxSatMod_zero_iff b v ⁅N, N⁆).2
        (foxSat_commutator b hcol N
          (fun w => (foxSatMod_zero_iff b w N).1 (hsat (w, ⟨0, Or.inl rfl⟩))) v)
    · haveI := Fact.mk hp
      exact foxSatMod_commutator m b hcol N (fun w => hsat (w, ⟨m, Or.inr hp⟩)) v
  cover_of_perfect := fun N hN hsat hperf =>
    cover N hN (fun v => (foxSatMod_zero_iff b v N).1 (hsat (v, ⟨0, Or.inl rfl⟩))) hperf

/-- **`(1) ⇒ (2)` of Theorem A** with the requirements (2.2) in full: the only remaining
inputs are the cell data of the chains (including the lifting of cycles modulo `m`), the
Hurewicz dictionary, and the construction of the cover. -/
theorem hasAcyclicRegularCover_of_cellDataMod {G : Type u} [Group G] {I J : Type u}
    (b : I → J → MonoidAlgebra ℤ G)
    (hfin : ∀ v : J →₀ MonoidAlgebra ℤ G, {i : I | foxBoundary b v i ≠ 0}.Finite)
    (hcol : ∀ j, {i : I | b i j ≠ 0}.Finite)
    (cellData : ∀ (c : ℕ → W.Cx) (n : ℕ), c 0 = K → IsZeroChain W c n →
      ∃ (Fund : ℕ → Type u) (_ : ∀ r, Group (Fund r)) (Gen Cell : ℕ → Type u)
        (h : ChainInput b n Fund Gen Cell), ∀ m : ℕ, CycleLiftsMod h m)
    (dict : ∀ (N : Subgroup G) [N.Normal],
      ∃ f : (N.map (QuotientGroup.mk' ⁅N, N⁆)) →* Multiplicative (foxCokernel b hcol N),
        Function.Injective f)
    (cover : ∀ N : Subgroup G, N.Normal → (∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v N) →
      ⁅N, N⁆ = N → HasAcyclicRegularCover W K)
    (h : HasZeroChains W K) : HasAcyclicRegularCover W K :=
  hasAcyclicRegularCover_of_hasZeroChains
    (necessityInputs_of_cellDataMod b hfin hcol cellData dict cover) h

end FiniteChains
