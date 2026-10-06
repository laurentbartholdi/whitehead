module

public import RequestProject.Pi2ExtensionInjective

@[expose] public section

/-!
# The extension theorems are not vacuous: the torus

The hypotheses of `FiniteChains.extCycle_hnn_span_of` — the images of `u` and `v` have
infinite order in the presented group — are satisfiable, and in the simplest instance the
conclusion is a familiar statement.  Take the presentation `⟨x | ⟩` of `ℤ` and adjoin a
stable letter `z` with the relator `z x z^{-1} x^{-1}`; the result is the standard
presentation `⟨x, z | [z,x]⟩` of the torus.  Since the old presentation has no two-cells, the
generation statement says that the torus presentation complex has no nonzero Fox cycles at
all, i.e. it is aspherical (`FiniteChains.torus_isFoxCycle_eq_zero`).
-/

namespace FiniteChains

open MonoidAlgebra

/-- The presentation `⟨x | ⟩` of the infinite cyclic group. -/
def rhoZ : Empty → FreeGroup (Fin 1) := Empty.elim

/-- The generator `x`. -/
def xZ : FreeGroup (Fin 1) := FreeGroup.of 0

theorem relSub_rhoZ : relSub rhoZ = ⊥ := by
  have : Set.range rhoZ = (∅ : Set (FreeGroup (Fin 1))) := Set.range_eq_empty _
  rw [relSub, this]
  refine le_antisymm (Subgroup.normalClosure_le_normal ?_) bot_le
  simp

/-- A homomorphism detecting the infinite order of `x`. -/
noncomputable def degZ : PresGroup rhoZ →* Multiplicative ℤ :=
  QuotientGroup.lift _ (FreeGroup.lift (fun _ : Fin 1 => Multiplicative.ofAdd (1 : ℤ)))
    (by rw [relSub_rhoZ]; exact fun x hx => by simp [Subgroup.mem_bot.1 hx])

theorem degZ_x : degZ (QuotientGroup.mk xZ) = Multiplicative.ofAdd (1 : ℤ) := by
  show FreeGroup.lift (fun _ : Fin 1 => Multiplicative.ofAdd (1 : ℤ)) xZ = _
  simp [xZ]

/-- The image of `x` in the presented group has infinite order. -/
theorem not_isOfFinOrder_xZ : ¬ IsOfFinOrder (QuotientGroup.mk xZ : PresGroup rhoZ) := by
  refine not_isOfFinOrder_of_map degZ ?_
  rw [degZ_x]
  exact not_isOfFinOrder_ofAdd_one

/-- **The torus presentation complex is aspherical.**  Adjoining a stable letter `z` with the
relator `z x z^{-1} = x` to `⟨x | ⟩` gives the standard presentation of the torus, and the
generation statement for the stable-letter extension shows that it has no nonzero Fox
cycles: `π₂` vanishes. -/
theorem torus_isFoxCycle_eq_zero
    (v : Option Empty → MonoidAlgebra ℤ (PresGroup (extRel rhoZ (hnnWord xZ xZ))))
    (hv : IsFoxCycle (extRel rhoZ (hnnWord xZ xZ)) v) : v = 0 := by
  have hspan := extCycle_hnn_span_of rhoZ xZ xZ not_isOfFinOrder_xZ not_isOfFinOrder_xZ hv
  have hset : {w : Option Empty → MonoidAlgebra ℤ (PresGroup (extRel rhoZ (hnnWord xZ xZ))) |
      ∃ y : Empty → MonoidAlgebra ℤ (PresGroup rhoZ), IsFoxCycle rhoZ y ∧
        w = extCycleImage rhoZ (hnnWord xZ xZ) y} ⊆ {0} := by
    rintro _ ⟨y, -, rfl⟩
    refine Set.mem_singleton_iff.2 ?_
    funext jo
    cases jo with
    | none => rfl
    | some j => exact j.elim
  have : v ∈ Submodule.span (MonoidAlgebra ℤ (PresGroup (extRel rhoZ (hnnWord xZ xZ))))
      ({0} : Set (Option Empty → MonoidAlgebra ℤ (PresGroup (extRel rhoZ (hnnWord xZ xZ))))) :=
    Submodule.span_mono hset hspan
  rwa [Submodule.span_zero_singleton, Submodule.mem_bot] at this

end FiniteChains
