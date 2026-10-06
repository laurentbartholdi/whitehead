module

public import RequestProject.NecessityAlgebraic
public import RequestProject.TorsionFreeGroupRing
public import RequestProject.ChainFormulaMod

@[expose] public section

/-!
# The cell-level chain data is consistent

`RequestProject/ChainFormula.lean` proves formula (2.3) from the structure `ChainInput`,
which records the cell-level data of a chain of two-complexes whose inclusions are zero on
`π₂`.  A statement proved from a structure is worthless if the structure can never be
inhabited, so this file exhibits a model: the two-complex with one one-cell and one
two-cell attached along the generator (a disc glued along the circle), whose fundamental
group is `ℤ` and whose Fox boundary matrix is `x - 1`.  Its second homotopy module
vanishes, because `ℤ[ℤ]` is a domain, so every inclusion of this complex into itself is
zero on `π₂` and chains of every length exist.

In particular `HasCellChains` — condition (1) of Theorem A, at cell level — is satisfiable
with a nonzero boundary matrix.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

/-- The fundamental group of the model complex. -/
abbrev ModelGroup := Multiplicative ℤ

/-- The Fox boundary matrix of the model complex: the single entry `x - 1`. -/
noncomputable def modelB : Unit → Unit → MonoidAlgebra ℤ ModelGroup :=
  fun _ _ => MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) 1 - 1

theorem modelB_ne_zero : modelB () () ≠ 0 := by
  intro h
  have happ : (MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) 1 - 1 :
      MonoidAlgebra ℤ ModelGroup).coeff (1 : ModelGroup) = 0 := by rw [← modelB, h]; rfl
  rw [show ((1 : MonoidAlgebra ℤ ModelGroup)) = MonoidAlgebra.single 1 1 from rfl] at happ
  rw [MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_single, Finsupp.sub_apply, Finsupp.single_apply] at happ
  have h1 : (Multiplicative.ofAdd (1 : ℤ)) ≠ (1 : ModelGroup) := by decide
  simp [h1] at happ

/-- Cycles of the model complex vanish: `ℤ[ℤ]` is a domain and the boundary is `x - 1`. -/
theorem model_cycle_eq_zero (u : Unit →₀ MonoidAlgebra ℤ ModelGroup)
    (hu : ∀ _a : Unit, ∑ c ∈ u.support, u c * modelB () c = 0) : u = 0 := by
  classical
  haveI : IsDomain (MonoidAlgebra ℤ ModelGroup) := intMonoidAlgebra_isDomain _
  by_contra hne
  have hmem : () ∈ u.support := by
    simp only [Finsupp.mem_support_iff]
    intro h0
    exact hne (Finsupp.ext fun _ => h0)
  have hsupp : u.support = {()} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hmem, fun x _ => rfl⟩
  have h := hu ()
  rw [hsupp, Finset.sum_singleton] at h
  rcases mul_eq_zero.1 h with h' | h'
  · exact (Finsupp.mem_support_iff.1 hmem) h'
  · exact modelB_ne_zero h'

/-- The model chain of length `n`: the complex with fundamental group `ℤ` and boundary
`x - 1`, included into itself. -/
noncomputable def modelChain (n : ℕ) :
    ChainInput modelB n (fun _ => ModelGroup) (fun _ => Unit) (fun _ => Unit) where
  phi _ := MonoidHom.id _
  psi _ := MonoidHom.id _
  phi_succ _ := rfl
  genIncl _ := id
  cellIncl _ := id
  cellIncl_injective _ := Function.injective_id
  cellStep _ := id
  cellStep_injective _ := Function.injective_id
  bdry _ _ _ := modelB () ()
  bdry_old := by
    intro r i j
    show modelB () () = MonoidAlgebra.mapDomain _ (modelB i j)
    rw [show ((MonoidHom.id ModelGroup) : ModelGroup → ModelGroup) = id from rfl,
      MonoidAlgebra.mapDomain_id]
  bdry_new := by
    intro r a ha
    exact absurd rfl (ha ())
  zero_pi2 := by
    intro r _ u hu
    rw [model_cycle_eq_zero u hu]
    simp

/-- **Condition (1) at cell level is satisfiable with a nonzero boundary matrix.** -/
theorem hasCellChains_modelB : HasCellChains modelB :=
  fun n => ⟨fun _ => ModelGroup, fun _ => inferInstance, fun _ => Unit, fun _ => Unit,
    ⟨modelChain n⟩⟩

/-!
## The lifting of cycles modulo `m` is consistent as well

Formula (2.3) modulo `m` (`RequestProject/ChainFormulaMod.lean`) uses, besides
`ChainInput`, the lifting of cycles modulo `m`.  The model below — one one-cell and one
two-cell whose boundary matrix is the unit of the group ring — satisfies the whole package:
it is a `ChainInput` with a nonzero boundary matrix and it satisfies `CycleLiftsMod m` for
every `m`, so the hypotheses used in the derivation of `(1) ⇒ (2)` are jointly
satisfiable.
-/

/-- The boundary matrix of the second model: the unit of the group ring. -/
noncomputable def modelOneB : Unit → Unit → MonoidAlgebra ℤ ModelGroup := fun _ _ => 1

theorem modelOneB_ne_zero : modelOneB () () ≠ 0 := one_ne_zero

/-- Over one cell, the boundary of a chain is its single coefficient. -/
theorem model_sum_one (u : Unit →₀ MonoidAlgebra ℤ ModelGroup) :
    ∑ c ∈ u.support, u c * modelOneB () c = u () := by
  classical
  by_cases h : u () = 0
  · have hu : u = 0 := Finsupp.ext fun _ => h
    rw [hu]
    simp
  · have hmem : () ∈ u.support := Finsupp.mem_support_iff.2 h
    have hsupp : u.support = {()} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨hmem, fun x _ => rfl⟩
    rw [hsupp, Finset.sum_singleton, modelOneB, mul_one]

/-- The second model chain of length `n`. -/
noncomputable def modelChainOne (n : ℕ) :
    ChainInput modelOneB n (fun _ => ModelGroup) (fun _ => Unit) (fun _ => Unit) where
  phi _ := MonoidHom.id _
  psi _ := MonoidHom.id _
  phi_succ _ := rfl
  genIncl _ := id
  cellIncl _ := id
  cellIncl_injective _ := Function.injective_id
  cellStep _ := id
  cellStep_injective _ := Function.injective_id
  bdry _ _ _ := modelOneB () ()
  bdry_old := by
    intro r i j
    show modelOneB () () = MonoidAlgebra.mapDomain _ (modelOneB i j)
    rw [show ((MonoidHom.id ModelGroup) : ModelGroup → ModelGroup) = id from rfl,
      MonoidAlgebra.mapDomain_id]
  bdry_new := by
    intro r a ha
    exact absurd rfl (ha ())
  zero_pi2 := by
    intro r _ u hu
    have h0 : u () = 0 := by
      have := hu ()
      rwa [model_sum_one u] at this
    have hu0 : u = 0 := Finsupp.ext fun _ => h0
    rw [hu0]
    simp

/-- **The lifting of cycles modulo `m` holds in the model**, for every `m`. -/
theorem cycleLiftsMod_modelChainOne (n m : ℕ) : CycleLiftsMod (modelChainOne n) m := by
  intro r _ u hu
  obtain ⟨w, hw⟩ := hu ()
  have hw' : u () = m • w := by
    rw [← model_sum_one u]
    exact hw
  refine ⟨0, fun a => ?_, Finsupp.single () w, ?_⟩
  · simp
  · refine Finsupp.ext fun x => ?_
    cases x
    rw [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply, zero_add, Finsupp.smul_apply,
      Finsupp.single_eq_same, hw']

/-- **The cell-level data of `(1) ⇒ (2)` is jointly satisfiable**, with a nonzero boundary
matrix: chains of every length, together with the lifting of cycles modulo every `m`. -/
theorem hasCellChains_modelOneB_withLifts :
    ∀ n : ℕ, ∃ (h : ChainInput modelOneB n (fun _ => ModelGroup) (fun _ => Unit)
      (fun _ => Unit)), ∀ m : ℕ, CycleLiftsMod h m :=
  fun n => ⟨modelChainOne n, fun m => cycleLiftsMod_modelChainOne n m⟩

end FiniteChains
