import RequestProject.Framework
import RequestProject.NecessityAlgebraic

/-!
# The hypotheses of `(1) ⇒ (2)` reduced to their genuinely topological part

`FiniteChains.NecessityInputs` collects the five inputs that Section 2 uses in order to
derive condition (2) of Theorem A from condition (1): formula (2.3), the finite determinacy
of the requirements, their stability under intersections of chains, Lemma 2.1, and the
identification of a perfect normal subgroup with an acyclic regular cover.

Three of those five are now theorems:

* formula (2.3) is `ChainInput.foxSat_of_not_foxSat` (`RequestProject/ChainFormula.lean`);
* finite determinacy is `foxSat_finitelyDetermined` (`RequestProject/FoxRequirement.lean`);
* the intersection step is `sat_sInf_of_finitelyDetermined`
  (`RequestProject/FinitelyDeterminedInf.lean`);
* Lemma 2.1 is `foxSat_commutator` (`RequestProject/FoxCommutator.lean`), given torsion
  freeness of `N/[N, N]`.

This file assembles them: a `NecessityInputs` for the Fox requirements is produced from
three inputs only, all of which are genuinely topological, namely

* `cellData` — a chain of two-complexes gives the cell-level data of `ChainInput`
  (fundamental groups, cells, and the Fox boundary matrices of the stages);
* `htf` — the universal-coefficient input, torsion freeness of `N/[N, N]`;
* `cover` — a perfect normal subgroup satisfying the requirements gives the acyclic
  regular cover (algebraically this is `cover_acyclic_of_foxSat`).
-/

namespace FiniteChains

open MonoidAlgebra

universe u

variable {W : TwoComplexData.{u}} {K : W.Cx}

/-- **`NecessityInputs` from the cell-level data of the chains.**  The three remaining
hypotheses are the topological ones; the whole of Section 2 is supplied by the theorems of
this development. -/
noncomputable def necessityInputs_of_cellData {G : Type u} [inst : Group G] {I J : Type u}
    (b : I → J → MonoidAlgebra ℤ G)
    (hfin : ∀ v : J →₀ MonoidAlgebra ℤ G, {i : I | foxBoundary b v i ≠ 0}.Finite)
    (hcol : ∀ j, {i : I | b i j ≠ 0}.Finite)
    (cellData : ∀ (c : ℕ → W.Cx) (n : ℕ), c 0 = K → IsZeroChain W c n →
      ∃ (Fund : ℕ → Type u) (_ : ∀ r, Group (Fund r)) (Gen Cell : ℕ → Type u),
        Nonempty (ChainInput b n Fund Gen Cell))
    (htf : ∀ (N : Subgroup G) [N.Normal], (∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v N) →
      IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆)))
    (cover : ∀ N : Subgroup G, N.Normal → (∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v N) →
      ⁅N, N⁆ = N → HasAcyclicRegularCover W K) :
    NecessityInputs W K where
  G := G
  grp := inst
  Req := J →₀ MonoidAlgebra ℤ G
  Sat := fun N v => FoxSat b v N
  chain_subgroups := by
    intro c n hc0 hc
    obtain ⟨Fund, instF, Gen, Cell, ⟨h⟩⟩ := cellData c n hc0 hc
    letI := instF
    exact ⟨fun r => (h.phi r).ker, fun r => inferInstance,
      fun r v hv s hrs hsn => h.foxSat_of_not_foxSat v r hv s hrs hsn⟩
  det := fun v => foxSat_finitelyDetermined b v (hfin v)
  sat_sInf_chain := fun C hchain hne hC =>
    sat_sInf_of_finitelyDetermined (fun N v => FoxSat b v N)
      (fun v => foxSat_finitelyDetermined b v (hfin v)) hchain hne
      (fun N hNmem => (hC N hNmem).2)
  sat_commutator := by
    intro N hN hsat
    haveI := hN
    haveI := htf N hsat
    exact foxSat_commutator b hcol N hsat
  cover_of_perfect := fun N hN hsat hperf => cover N hN hsat hperf

/-- With the cell-level data available, `(1) ⇒ (2)` of Theorem A holds. -/
theorem hasAcyclicRegularCover_of_cellData {G : Type u} [Group G] {I J : Type u}
    (b : I → J → MonoidAlgebra ℤ G)
    (hfin : ∀ v : J →₀ MonoidAlgebra ℤ G, {i : I | foxBoundary b v i ≠ 0}.Finite)
    (hcol : ∀ j, {i : I | b i j ≠ 0}.Finite)
    (cellData : ∀ (c : ℕ → W.Cx) (n : ℕ), c 0 = K → IsZeroChain W c n →
      ∃ (Fund : ℕ → Type u) (_ : ∀ r, Group (Fund r)) (Gen Cell : ℕ → Type u),
        Nonempty (ChainInput b n Fund Gen Cell))
    (htf : ∀ (N : Subgroup G) [N.Normal], (∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v N) →
      IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆)))
    (cover : ∀ N : Subgroup G, N.Normal → (∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v N) →
      ⁅N, N⁆ = N → HasAcyclicRegularCover W K)
    (h : HasZeroChains W K) : HasAcyclicRegularCover W K :=
  hasAcyclicRegularCover_of_hasZeroChains
    (necessityInputs_of_cellData b hfin hcol cellData htf cover) h

end FiniteChains
