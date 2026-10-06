import RequestProject.InitialChain
import RequestProject.PresCockcroftDictionary
import RequestProject.PresentationComplexAcyclic
import RequestProject.CombHurewicz1Pres
import RequestProject.TheoremAAcyclic

/-!
# The initial pair of Lemma 3.1 as a map-carrying relative chain

`RequestProject/InitialComplex.lean` proves Lemma 3.1 for the complex
`Y_D = ⟨x_i, a_i, b_i | r_j, x_i[a_i,b_i]⁻¹, [y_{i,s}, y_{k,t}]⟩` attached to an acyclic
complex `D` of a finite presentation: `Y_D` is Cockcroft, the inclusion `D ⊂ Y_D` kills
`π₁(D)` and is zero on `π₂`.

The reverse implication of Theorem A uses the extension step in the map-carrying form
`FiniteChains.Comb.RelChainW` of `RequestProject/MapChainDescent.lean`: a relative chain over
`D` together with its inclusions, the Cockcroft property of every stage, the finiteness
bookkeeping and the requirement that each step adds a two-cell.  This file assembles Lemma 3.1
into exactly that shape, giving **the base case, of length one, of the extension step
`FiniteChains.Comb.MapStep`**:

* `FiniteChains.Comb.initialSeq`, `FiniteChains.Comb.initialInclHom`,
  `FiniteChains.Comb.initialInc` — the pair `D ⊂ Y_D` as a sequence of complexes with its
  inclusions;
* `FiniteChains.Comb.initialRelChainW` — that pair as a `RelChainW` of length one;
* `FiniteChains.Comb.nonempty_relChainW_initial_one` — hence, over the presentation complex of
  a finite acyclic presentation with at least one generator, there is a map-carrying relative
  chain of length one;
* `FiniteChains.Comb.isAcyclic_presComplex_of_exp` — a presentation complex whose exponent-sum
  matrix is bijective is acyclic;
* `FiniteChains.Comb.nonempty_strictTopChain_zero_initial` — combining the two with the
  generation statement (3.5) for the identity covering: **condition (1) of Theorem A of length
  one, unconditionally**, for the presentation complex of a finite acyclic presentation with at
  least one generator.
-/

namespace FiniteChains
namespace Comb

universe u

variable {I J : Type u} [LinearOrder I] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (r : J → FreeGroup I)

omit [Fintype I] [Fintype J] [DecidableEq J] in
/-- The two stages of the initial pair: `D` and `Y_D` (the chain is extended by repeating
`Y_D`). -/
def initialSeq : ℕ → Complex2.{u}
  | 0 => presComplex r
  | _ + 1 => presComplex (relY r)

/-- The inclusion `D ⊂ Y_D` as a cellular map. -/
def initialInclHom : Hom (presComplex r) (presComplex (relY r)) :=
  presInclHom (Sum.inl : I → GenY I) Sum.inl_injective r (relY r) (Sum.inl : J → CellY I J)
    (fun _ => rfl)

/-- The inclusions of the sequence `D ⊂ Y_D = Y_D = ⋯`. -/
def initialInc : ∀ i, Hom (initialSeq r i) (initialSeq r (i + 1))
  | 0 => initialInclHom r
  | _ + 1 => Hom.id _

omit [Fintype J] [DecidableEq J] in
theorem finite_initialSeq_E (i : ℕ) : Finite (initialSeq r i).E := by
  cases i with
  | zero => exact Finite.of_fintype I
  | succ k => exact Finite.of_fintype (GenY I)

omit [DecidableEq J] in
theorem finite_initialSeq_F (i : ℕ) : Finite (initialSeq r i).F := by
  cases i with
  | zero => exact Finite.of_fintype J
  | succ k => exact Finite.of_fintype (CellY I J)

theorem isConnected_presComplex' {α J' : Type u} [DecidableEq α] (ρ : J' → FreeGroup α) :
    IsConnected (presComplex ρ) := fun _ _ => ⟨[], isPath_of_subsingleton _ _ _ _ _⟩

omit [Fintype I] [Fintype J] [DecidableEq J] in
theorem isConnected_initialSeq (i : ℕ) : IsConnected (initialSeq r i) := by
  cases i with
  | zero => exact isConnected_presComplex' r
  | succ k => exact isConnected_presComplex' (relY r)

theorem isCockcroft_initialSeq (hMs : ExpSurjective r) (hMi : ExpInjective r) (i : ℕ) :
    IsCockcroft (initialSeq r i) := by
  cases i with
  | zero => exact (isCockcroft_presComplex_iff r).2 (isCockcroft_of_expInjective r hMi)
  | succ k => exact (isCockcroft_presComplex_iff (relY r)).2 (isCockcroft_relY hMs hMi)

/-- **The inclusion `D ⊂ Y_D` is zero on `π₂`** in the combinatorial reading (Lemma 3.1). -/
theorem zeroPi2_initialInclHom (hMs : ExpSurjective r) (hMi : ExpInjective r) :
    ZeroPi2 (initialInclHom r) :=
  (zeroPi2_presInclHom_iff (ρ := r) (σ := relY r) (f := (Sum.inl : I → GenY I))
    (hf := Sum.inl_injective) (g := (Sum.inl : J → CellY I J))
    (hg := fun _ => rfl)).2 fun v hv => zero_pi2_initial hMs hMi v hv

omit [Fintype I] [Fintype J] [DecidableEq J] in
/-- **The inclusion `D ⊂ Y_D` kills `π₁(D)`** (Lemma 3.1). -/
theorem pi1Trivial_initialInclHom (hMs : ExpSurjective r) : Pi1Trivial (initialInclHom r) :=
  (pi1Trivial_presInclHom_iff (ρ := r) (σ := relY r) (f := (Sum.inl : I → GenY I))
    (hf := Sum.inl_injective) (g := (Sum.inl : J → CellY I J))
    (hg := fun _ => rfl)).2 fun w => presMapY_eq_one hMs w

/-- **The initial pair of Lemma 3.1 as a map-carrying relative chain of length one.** -/
def initialRelChainW [Nonempty I] (hMs : ExpSurjective r) (hMi : ExpInjective r) :
    RelChainW (presComplex r) (initialSeq r) 1 where
  inc := initialInc r
  incV := by
    intro i a b _
    cases i <;> exact Subsingleton.elim (α := PUnit.{u + 1}) a b
  incE := by
    intro i
    cases i with
    | zero => exact Sum.inl_injective
    | succ k => exact Function.injective_id
  incF := by
    intro i
    cases i with
    | zero => exact Sum.inl_injective
    | succ k => exact Function.injective_id
  base := rfl
  conn := isConnected_initialSeq r
  cockcroft := fun i _ => isCockcroft_initialSeq r hMs hMi i
  zero := by
    intro i hi
    interval_cases i
    exact zeroPi2_initialInclHom r hMs hMi
  pi1 := by
    intro i h1 h2
    interval_cases i
    exact pi1Trivial_initialInclHom r hMs
  finE := by
    intro i
    have := finite_initialSeq_E r i
    exact Subtype.finite
  finF := by
    intro i
    have := finite_initialSeq_F r i
    exact Subtype.finite
  adds := by
    intro i hi
    interval_cases i
    obtain ⟨i₀⟩ := ‹Nonempty I›
    exact ⟨⟨Sum.inr (Sum.inl i₀), fun _ h => by cases h⟩⟩

/-- **The base case of the extension step.**  Over the presentation complex of a finite
acyclic presentation with at least one generator there is a map-carrying relative chain of
length one: the initial pair `D ⊂ Y_D` of Lemma 3.1. -/
theorem nonempty_relChainW_initial_one [Nonempty I] (hMs : ExpSurjective r)
    (hMi : ExpInjective r) :
    ∃ c : ℕ → Complex2.{u}, Nonempty (RelChainW (presComplex r) c 1) :=
  ⟨initialSeq r, ⟨initialRelChainW r hMs hMi⟩⟩

/-! ### Acyclicity of the presentation complex, read off the exponent-sum matrix -/

omit [LinearOrder I] [Fintype I] [Fintype J] [DecidableEq J] in
theorem bdry2_presComplex_eq_expCol :
    bdry2 (presComplex r) = Finsupp.linearCombination ℤ (expCol r) := by
  refine Finsupp.lhom_ext' fun j => LinearMap.ext_ring ?_
  show bdry2 (presComplex r) (Finsupp.single j (1 : ℤ))
    = Finsupp.linearCombination ℤ (expCol r) (Finsupp.single j (1 : ℤ))
  rw [bdry2_pres_single, Finsupp.linearCombination_single, one_smul, expCol_eq_expVec]
  rfl

omit [LinearOrder I] [Fintype I] [DecidableEq J] in
theorem injective_bdry2_presComplex (hMi : ExpInjective r) :
    Function.Injective (bdry2 (presComplex r)) := by
  classical
  rw [bdry2_presComplex_eq_expCol]
  refine (injective_iff_map_eq_zero' _).2 fun c => ⟨fun hc => ?_, fun hc => by rw [hc, map_zero]⟩
  have hcoord : ∀ i : I, ∑ j : J, c j * expEntry r i j = 0 := by
    intro i
    have h := congrArg (fun v : I →₀ ℤ => v i) hc
    have hsum : (Finsupp.linearCombination ℤ (expCol r) c) i
        = ∑ j : J, c j * expEntry r i j := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      rw [Finsupp.finset_sum_apply]
      refine (Finset.sum_subset (Finset.subset_univ _) ?_).trans ?_
      · intro j _ hj
        have : c j = 0 := by simpa using hj
        simp [this]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finsupp.smul_apply, smul_eq_mul, expCol_eq_expVec, expVec_apply]
        rfl
    rw [← hsum]
    simpa using h
  exact Finsupp.ext fun j => hMi (fun j => c j) hcoord j

omit [LinearOrder I] [Fintype I] [Fintype J] [DecidableEq J] in
theorem surjective_bdry2_presComplex (hMs : ExpSurjective r) :
    Function.Surjective (bdry2 (presComplex r)) := by
  rw [bdry2_presComplex_eq_expCol]
  exact hMs

omit [LinearOrder I] [Fintype I] [DecidableEq J] in
/-- **A presentation complex whose exponent-sum matrix is bijective is acyclic.** -/
theorem isAcyclic_presComplex_of_exp (hMs : ExpSurjective r) (hMi : ExpInjective r) :
    IsAcyclic (presComplex r) :=
  (isAcyclic_presentationComplex_iff (w := fun j => (r j).toWord)).2
    ⟨injective_bdry2_presComplex r hMi, surjective_bdry2_presComplex r hMs⟩

/-- **An unconditional strict extension of an acyclic presentation complex.**  Lemma 3.1
produces, over the presentation complex `D` of a finite acyclic presentation with at least one
generator, a strictly larger finite complex whose inclusion is zero on `π₂` — that is,
condition (1) of Theorem A of length one, with no unproved hypothesis. -/
theorem nonempty_strictTopChain_zero_initial [Nonempty I] (hMs : ExpSurjective r)
    (hMi : ExpInjective r) : Nonempty (StrictTopChain (presComplex r) 0) := by
  have hacyc : IsAcyclic (presComplex r) := isAcyclic_presComplex_of_exp r hMs hMi
  exact ⟨strictTopChain_of_relChainW (initialRelChainW r hMs hMi) (Hom.id (presComplex r))
    (isCovering_id _) hacyc (isConnected_presComplex' r) (Finite.of_fintype I)
    (Finite.of_fintype J) PUnit.unit (pi2GeneratedByUpstairsFor_id _)⟩

/-! ### The hypotheses are satisfiable -/

/-- The initial pair is not vacuous: for the acyclic presentation `⟨x | x⟩` there is a
map-carrying relative chain of length one. -/
theorem nonempty_relChainW_initial_trivial :
    ∃ c : ℕ → Complex2.{0}, Nonempty (RelChainW (presComplex trivialPres) c 1) :=
  nonempty_relChainW_initial_one trivialPres expSurjective_trivialPres expInjective_trivialPres

/-- Likewise the unconditional strict extension is not vacuous. -/
theorem nonempty_strictTopChain_zero_trivial :
    Nonempty (StrictTopChain (presComplex trivialPres) 0) :=
  nonempty_strictTopChain_zero_initial trivialPres expSurjective_trivialPres
    expInjective_trivialPres

end Comb
end FiniteChains
