import RequestProject.Isolator
import RequestProject.FrameworkNecessityMod

/-!
# An unconditional consequence of Section 2: torsion abelianization

The derivation of `(1) ⇒ (2)` in Section 2 runs as follows: chains of every finite length
give, by the one-violation principle, a normal subgroup meeting any finite family of the
requirements (2.2); compactness produces one normal subgroup meeting all of them;
minimality produces a minimal such subgroup `N`; Lemma 2.1 then shows `[N, N]` still meets
all requirements, so minimality forces `N = [N, N]`, i.e. `N` is perfect.

The last step uses that `N/[N, N]` is torsion free, which the paper takes from the
universal coefficient theorem through the dictionary `H₁(K_N) = N/[N, N]`.  Without any
such input one still gets, unconditionally, the following weaker conclusion, because
Lemma 2.1 applies to the isolator of `[N, N]` in `N` with no hypothesis at all
(`RequestProject/Isolator.lean`):

> the minimal normal subgroup `N` satisfying the requirements (2.2) has **torsion**
> abelianization: every element of `N` has a positive power in `[N, N]`.

Perfectness of `N` is exactly the statement that this torsion group is trivial.
-/

namespace FiniteChains

open MonoidAlgebra

universe u

variable {W : TwoComplexData.{u}} {K : W.Cx}

/-- **The minimal subgroup of Section 2 has torsion abelianization**, unconditionally.
If every finite family of the requirements (2.2) is met by some normal subgroup, then some
normal subgroup meets all of them and every element of it has a positive power in its
commutator subgroup. -/
theorem exists_normal_foxSatMod_torsion_abelianization {G : Type u} [Group G] {I J : Type u}
    (b : I → J → MonoidAlgebra ℤ G)
    (hfin : ∀ v : J →₀ MonoidAlgebra ℤ G, {i : I | foxBoundary b v i ≠ 0}.Finite)
    (hcol : ∀ j, {i : I | b i j ≠ 0}.Finite)
    (hfamily : ∀ S : Finset (ReqMod G J), ∃ N : Subgroup G, N.Normal ∧
      ∀ vm ∈ S, FoxSatMod vm.2.1 b vm.1 N) :
    ∃ N : Subgroup G, N.Normal ∧ (∀ vm : ReqMod G J, FoxSatMod vm.2.1 b vm.1 N) ∧
      ∀ x ∈ N, ∃ k : ℕ, 0 < k ∧ x ^ k ∈ ⁅N, N⁆ := by
  classical
  have hdet : FinitelyDetermined (fun (N : Subgroup G) (vm : ReqMod G J) =>
      FoxSatMod vm.2.1 b vm.1 N) :=
    fun vm => foxSatMod_finitelyDetermined vm.2.1 b vm.1 (hfin vm.1)
  obtain ⟨M, hMnormal, hM⟩ :=
    exists_normal_subgroup_forall (fun (N : Subgroup G) (vm : ReqMod G J) =>
      FoxSatMod vm.2.1 b vm.1 N) hdet hfamily
  obtain ⟨N, -, hNnormal, hN, hNmin⟩ :=
    exists_minimal_normal_sat (fun N => ∀ vm : ReqMod G J, FoxSatMod vm.2.1 b vm.1 N)
      (fun C hchain hne hC =>
        sat_sInf_of_finitelyDetermined
          (fun (N : Subgroup G) (vm : ReqMod G J) => FoxSatMod vm.2.1 b vm.1 N) hdet hchain hne
          (fun N hNmem => (hC N hNmem).2))
      M hMnormal hM
  haveI := hNnormal
  have hiso : isolatorComm N = N :=
    hNmin (isolatorComm N) (isolatorComm_le N) inferInstance
      (fun vm => foxSatMod_isolatorComm vm.2.1 vm.2.2 b hcol N (fun v => hN (v, vm.2)) vm.1)
  refine ⟨N, hNnormal, hN, ?_⟩
  intro x hx
  rw [← hiso] at hx
  obtain ⟨-, k, hk, hxk⟩ := mem_isolatorComm.1 hx
  exact ⟨k, hk, hxk⟩

/-- **The same conclusion from condition (1) of Theorem A**: a chain of two-complexes of
every finite length over `K` produces a normal subgroup of `G = π₁(K)` satisfying all the
requirements (2.2), integrally and modulo every prime, whose abelianization is a torsion
group.  The only input is the cell-level data of the chains. -/
theorem exists_normal_foxSatMod_torsion_of_hasZeroChains {G : Type u} [Group G] {I J : Type u}
    (b : I → J → MonoidAlgebra ℤ G)
    (hfin : ∀ v : J →₀ MonoidAlgebra ℤ G, {i : I | foxBoundary b v i ≠ 0}.Finite)
    (hcol : ∀ j, {i : I | b i j ≠ 0}.Finite)
    (cellData : ∀ (c : ℕ → W.Cx) (n : ℕ), c 0 = K → IsZeroChain W c n →
      ∃ (Fund : ℕ → Type u) (_ : ∀ r, Group (Fund r)) (Gen Cell : ℕ → Type u)
        (h : ChainInput b n Fund Gen Cell), ∀ m : ℕ, CycleLiftsMod h m)
    (hchains : HasZeroChains W K) :
    ∃ N : Subgroup G, N.Normal ∧ (∀ vm : ReqMod G J, FoxSatMod vm.2.1 b vm.1 N) ∧
      ∀ x ∈ N, ∃ k : ℕ, 0 < k ∧ x ^ k ∈ ⁅N, N⁆ := by
  classical
  refine exists_normal_foxSatMod_torsion_abelianization b hfin hcol ?_
  intro S
  obtain ⟨c, hc0, hc⟩ := hchains S.card
  obtain ⟨Fund, instF, Gen, Cell, hchain, hlift⟩ := cellData c S.card hc0 hc
  letI := instF
  obtain ⟨r, -, hr⟩ :=
    exists_stage_satisfying_all S le_rfl
      (fun r vm => FoxSatMod vm.2.1 b vm.1 (hchain.phi r).ker)
      (fun r vm hv s hrs hsn =>
        hchain.foxSatMod_of_not_foxSatMod vm.2.1 (hlift vm.2.1) vm.1 r hv s hrs hsn)
  exact ⟨(hchain.phi r).ker, inferInstance, hr⟩

end FiniteChains
