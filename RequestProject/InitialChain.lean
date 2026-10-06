module

public import RequestProject.InitialComplex
public import RequestProject.PresentationChain

@[expose] public section

/-!
# The initial pair as a chain of presentation complexes

`RequestProject/InitialComplex.lean` builds, over an acyclic complex `D` of a finite
presentation, the complex `Y_D` of Lemma 3.1 and proves the three assertions of that lemma:
`G(Y_D)` is free abelian on the added pairs of generators, `Y_D` is Cockcroft, and the
inclusion `D ⊂ Y_D` kills `π₁(D)` and is zero on `π₂`.

This file records the resulting pair as a genuine object of the framework of
`RequestProject/PresentationChain.lean`: `D ⊂ Y_D` is a chain
`FiniteChains.PresChain r 1` of nested presentation complexes whose single inclusion is
zero on `π₂`, i.e. the first step of condition (1) of Theorem A.  In particular the
hypothesis `zero_pi2` demanded there is exactly what Lemma 3.1 provides.
-/

namespace FiniteChains

universe u

variable {I J : Type u} [LinearOrder I] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The generators of the stages of the chain `D ⊂ Y_D`. -/
def genSeq (I : Type u) : ℕ → Type u
  | 0 => I
  | _ + 1 => GenY I

/-- The two-cells of the stages of the chain `D ⊂ Y_D`. -/
def cellSeq (I J : Type u) [LinearOrder I] : ℕ → Type u
  | 0 => J
  | _ + 1 => CellY I J

instance instDecGenSeq (k : ℕ) [DecidableEq I] : DecidableEq (genSeq I k) := by
  cases k <;> unfold genSeq <;> infer_instance

instance instFinGenSeq (k : ℕ) [Fintype I] [DecidableEq I] : Fintype (genSeq I k) := by
  cases k <;> unfold genSeq <;> infer_instance

instance instFinCellSeq (k : ℕ) [Fintype I] [DecidableEq I] [Fintype J] :
    Fintype (cellSeq I J k) := by
  cases k <;> unfold cellSeq <;> infer_instance

/-- The attaching words of the stages. -/
def relSeq (r : J → FreeGroup I) : ∀ k, cellSeq I J k → FreeGroup (genSeq I k)
  | 0 => r
  | _ + 1 => relY r

/-- The inclusions of the generating sets. -/
def genInclSeq (I : Type u) : ∀ k, genSeq I k → genSeq I (k + 1)
  | 0 => Sum.inl
  | _ + 1 => id

/-- The inclusions of the sets of two-cells. -/
def cellInclSeq (I J : Type u) [LinearOrder I] : ∀ k, cellSeq I J k → cellSeq I J (k + 1)
  | 0 => Sum.inl
  | _ + 1 => id

/-- **The initial pair `D ⊂ Y_D` of Lemma 3.1 is a chain of presentation complexes of
length one**: the two-cells and generators of `D` are retained, the old cells are attached
along the same words, and the inclusion is zero on `π₂`. -/
noncomputable def initialPresChain {r : J → FreeGroup I} (hMs : ExpSurjective r)
    (hMi : ExpInjective r) : PresChain r 1 where
  gen := genSeq I
  cell := cellSeq I J
  decGen k := instDecGenSeq k
  finGen k := instFinGenSeq k
  finCell k := instFinCellSeq k
  rel := relSeq r
  genIncl := genInclSeq I
  genIncl_injective k := by
    cases k with
    | zero => exact Sum.inl_injective
    | succ n => exact Function.injective_id
  cellIncl := cellInclSeq I J
  cellIncl_injective k := by
    cases k with
    | zero => exact Sum.inl_injective
    | succ n => exact Function.injective_id
  rel_incl k c := by
    cases k with
    | zero => rfl
    | succ n => exact (FreeGroup.map.id _).symm
  baseGen := id
  baseGen_injective := Function.injective_id
  baseCell := id
  baseCell_injective := Function.injective_id
  rel_base j := (FreeGroup.map.id _).symm
  zero_pi2 k hk u hu := by
    match k, hk with
    | 0, _ => exact zero_pi2_initial hMs hMi u hu

/-- **Over an acyclic complex `D` there is a chain of presentation complexes of length one
whose inclusion is zero on `π₂`** — the initial pair of Lemma 3.1. -/
theorem nonempty_presChain_one {r : J → FreeGroup I} (hMs : ExpSurjective r)
    (hMi : ExpInjective r) : Nonempty (PresChain r 1) :=
  ⟨initialPresChain hMs hMi⟩

/-! ### The hypotheses are satisfiable -/

/-- The presentation `⟨x | x⟩`, whose complex is acyclic. -/
def trivialPres : Fin 1 → FreeGroup (Fin 1) := fun _ => FreeGroup.of 0

theorem expSurjective_trivialPres : ExpSurjective trivialPres := by
  intro y
  refine ⟨Finsupp.single 0 (y 0), ?_⟩
  have hcol : expCol trivialPres 0 = Finsupp.single 0 (1 : ℤ) := by
    show Multiplicative.toAdd (expVecHom (FreeGroup.of 0)) = _
    exact expVecHom_of 0
  rw [Finsupp.linearCombination_single, hcol, Finsupp.smul_single, smul_eq_mul, mul_one]
  refine Finsupp.ext fun i => ?_
  rw [Finsupp.single_apply]
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  simp

theorem expInjective_trivialPres : ExpInjective trivialPres := by
  intro c hc j
  have h := hc 0
  have hentry : expEntry trivialPres 0 0 = 1 := by
    show Multiplicative.toAdd (expSum 0 (FreeGroup.of 0)) = 1
    simp
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_univ 0)
      (fun b _ hb => absurd (Subsingleton.elim b 0) hb), hentry, mul_one] at h
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  exact h

/-- The hypotheses of Lemma 3.1 are satisfiable, so the results above are not proved
vacuously. -/
theorem nonempty_presChain_one_trivial : Nonempty (PresChain trivialPres 1) :=
  nonempty_presChain_one expSurjective_trivialPres expInjective_trivialPres

end FiniteChains
