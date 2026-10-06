import RequestProject.PresentationChain

/-!
# Chains of presentation complexes exist

`RequestProject/PresentationChain.lean` derives `(1) ⇒ (2)` for a presented complex from
the existence of chains `K = X₀ ⊂ ⋯ ⊂ Xₙ` of presentation complexes with the two
topological properties.  A statement derived from hypotheses is worthless if they can never
be met, so this file exhibits such chains: for the presentation `⟨x | x⟩` the constant
chain is one, for every length.

Consequently the complex of `⟨x | x⟩` has a connected acyclic regular cover, by the general
theorem and not by inspection.
-/

namespace FiniteChains

open MonoidAlgebra

/-- In the model below the boundary matrix has the single entry `1`. -/
theorem quot_fox_unit :
    quotRingHom ℤ (relSub (fun _ : Unit => FreeGroup.of ()))
        (fox () (FreeGroup.of (α := Unit) ())) = 1 := by
  rw [show fox () (FreeGroup.of (α := Unit) ()) = 1 by simp, map_one]

/-- Over one two-cell the boundary of a chain is its single coefficient. -/
theorem unit_coeff_sum {R : Type*} [Ring R] (u : Unit →₀ R) :
    ∑ c ∈ u.support, u c * (1 : R) = u () := by
  classical
  by_cases h : u () = 0
  · have hu : u = 0 := Finsupp.ext fun _ => h
    rw [hu]
    simp
  · have hsupp : u.support = {()} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨Finsupp.mem_support_iff.2 h, fun x _ => rfl⟩
    rw [hsupp, Finset.sum_singleton, mul_one]

/-- The constant chain over the presentation `⟨x | x⟩`: every stage is the complex itself. -/
noncomputable def unitPresChain (n : ℕ) : PresChain presRho n where
  gen _ := Unit
  cell _ := Unit
  decGen _ := inferInstance
  finGen _ := inferInstance
  finCell _ := inferInstance
  rel _ _ := FreeGroup.of ()
  genIncl _ := id
  genIncl_injective _ := Function.injective_id
  cellIncl _ := id
  cellIncl_injective _ := Function.injective_id
  rel_incl _ _ := by simp
  baseGen := id
  baseGen_injective := Function.injective_id
  baseCell := id
  baseCell_injective := Function.injective_id
  rel_base _ := by simp [presRho]
  zero_pi2 := by
    intro r _
    refine (Comb.univCover_zero_pi2_iff (fun _ : Unit => FreeGroup.of ()) _ id
      Function.injective_id).2 ?_
    intro v hv
    have h0 : v () = 0 := by
      have h := hv ()
      have hone : ∀ c : Unit, foxMatrixPres (fun _ : Unit => FreeGroup.of ()) () c = 1 :=
        fun _ => quot_fox_unit
      simp only [hone] at h
      rwa [unit_coeff_sum v] at h
    have hv0 : v = 0 := Finsupp.ext fun _ => h0
    rw [hv0]
    simp

/-- **The chain hypothesis is satisfiable**: over `⟨x | x⟩` there are chains of presentation
complexes of every length. -/
theorem nonempty_presChain_presRho (n : ℕ) : Nonempty (PresChain presRho n) :=
  ⟨unitPresChain n⟩

/-- Hence the general theorem applies and produces a connected acyclic regular cover of the
complex of `⟨x | x⟩`. -/
theorem presComplex_presRho_hasAcyclicRegularCover_of_presChains :
    Comb.HasAcyclicRegularCover (Comb.presComplex presRho) :=
  presComplex_hasAcyclicRegularCover_of_presChains presRho nonempty_presChain_presRho

end FiniteChains
