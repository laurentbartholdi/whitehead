import RequestProject.PresentationDictionary
import RequestProject.ChainConsistency

/-!
# The presented form of `(1) ⇒ (2)` is not vacuous

`RequestProject/PresentationDictionary.lean` derives the implication `(1) ⇒ (2)` of
Theorem A for a presented complex from two topological inputs, the first of which is the
cell data of the chains.  A statement derived from hypotheses is worthless if the
hypotheses can never be met, so this file exhibits a presentation for which the cell data
(together with the lifting of cycles modulo every `m`) does exist: the presentation
`⟨x | x⟩`, whose Fox boundary matrix is the unit of the group ring.

The construction is the one of `RequestProject/ChainConsistency.lean`, carried out over an
arbitrary group so that it can be applied to `G = π₁(K)` of the presentation.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra

section UnitModel

variable (Gm : Type) [Group Gm]

/-- The boundary matrix of the model: one one-cell, one two-cell, boundary the unit of the
group ring. -/
noncomputable def unitB : Unit → Unit → MonoidAlgebra ℤ Gm := fun _ _ => 1

theorem unitB_ne_zero : unitB Gm () () ≠ 0 := one_ne_zero

variable {Gm}

/-- Over one cell the boundary of a chain is its single coefficient. -/
theorem unit_sum_one (u : Unit →₀ MonoidAlgebra ℤ Gm) :
    ∑ c ∈ u.support, u c * unitB Gm () c = u () := by
  classical
  by_cases h : u () = 0
  · have hu : u = 0 := Finsupp.ext fun _ => h
    rw [hu]
    simp
  · have hmem : () ∈ u.support := Finsupp.mem_support_iff.2 h
    have hsupp : u.support = {()} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨hmem, fun x _ => rfl⟩
    rw [hsupp, Finset.sum_singleton, unitB, mul_one]

variable (Gm)

/-- The model chain of length `n` over the group `Gm`. -/
noncomputable def unitChain (n : ℕ) :
    ChainInput (unitB Gm) n (fun _ => Gm) (fun _ => Unit) (fun _ => Unit) where
  phi _ := MonoidHom.id _
  psi _ := MonoidHom.id _
  phi_succ _ := rfl
  genIncl _ := id
  cellIncl _ := id
  cellIncl_injective _ := Function.injective_id
  cellStep _ := id
  cellStep_injective _ := Function.injective_id
  bdry _ _ _ := unitB Gm () ()
  bdry_old := by
    intro r i j
    show unitB Gm () () = MonoidAlgebra.mapDomain _ (unitB Gm i j)
    rw [show ((MonoidHom.id Gm) : Gm → Gm) = id from rfl, MonoidAlgebra.mapDomain_id]
  bdry_new := by
    intro r a ha
    exact absurd rfl (ha ())
  zero_pi2 := by
    intro r _ u hu
    have h0 : u () = 0 := by
      have := hu ()
      rwa [unit_sum_one u] at this
    have hu0 : u = 0 := Finsupp.ext fun _ => h0
    rw [hu0]
    simp

/-- The lifting of cycles modulo `m` holds in the model, for every `m`. -/
theorem cycleLiftsMod_unitChain (n m : ℕ) : CycleLiftsMod (unitChain Gm n) m := by
  intro r _ u hu
  obtain ⟨w, hw⟩ := hu ()
  have hw' : u () = m • w := by
    rw [← unit_sum_one u]
    exact hw
  refine ⟨0, fun a => ?_, Finsupp.single () w, ?_⟩
  · simp
  · refine Finsupp.ext fun x => ?_
    cases x
    rw [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply, zero_add, Finsupp.smul_apply,
      Finsupp.single_eq_same, hw']

end UnitModel

/-! ### The presentation `⟨x | x⟩` -/

/-- The presentation `⟨x | x⟩`: one generator, one relator equal to that generator. -/
noncomputable def presRho : Unit → FreeGroup Unit := fun _ => FreeGroup.of ()

/-- Its Fox boundary matrix is the unit of the group ring. -/
theorem foxMatrixPres_presRho : foxMatrixPres presRho = unitB (PresGroup presRho) := by
  funext i j
  cases i; cases j
  show quotRingHom ℤ (relSub presRho) (fox () (presRho ())) = 1
  rw [presRho, fox_of, if_pos rfl, map_one]

/-- **The cell data required by the presented form of `(1) ⇒ (2)` is satisfiable**, with a
nonzero boundary matrix: for the presentation `⟨x | x⟩` there are chains of every length
together with the lifting of cycles modulo every `m`. -/
theorem exists_chainInput_presRho (n : ℕ) :
    ∃ h : ChainInput (foxMatrixPres presRho) n (fun _ => PresGroup presRho)
      (fun _ => Unit) (fun _ => Unit), ∀ m : ℕ, CycleLiftsMod h m := by
  rw [foxMatrixPres_presRho]
  exact ⟨unitChain (PresGroup presRho) n, fun m => cycleLiftsMod_unitChain _ n m⟩

end FiniteChains
