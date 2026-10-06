import RequestProject.BlockFamilyFactorComparison
import RequestProject.GenusMarkedSpineFamily

/-!
# The actual spine factors embed in the simultaneous substituted group

This specializes the wide-amalgam comparison to the constructed finite spines.
The single-factor fillings and injectivity are supplied by the established
geometric spine construction, rather than required as new hypotheses.


-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus

open RACG Mirror Comb PresModel BlockFamily

noncomputable section

variable {α Jr Sx : Type} (ρ : Jr ⊕ Sx → FreeGroup α)
  (q : Sx → ℕ) [∀ s, NeZero (q s)]
  (u : ∀ s, Fin (q s) × Bool → FreeGroup α)
  (hrho : ∀ s, ρ (Sum.inr s) = commWord (u s) (finitePairs (q s)))

include hrho in
/-- The genuine fillings in each individual substitution. -/
theorem finiteSpineIndividualFillings :
    ∀ s, FilledF (oneRel ρ s)
      (fun _ : PUnit.{1} => familyFiniteSpineWordBlock q u s) :=
  fun s => finiteSpineWordBlock_filled (oneRel ρ s) (q s) (u s) (hrho s)

/-- The common original group in the actual wide diagram of individual spines. -/
def finiteSpineIndividualBase (s : Sx) :
    PresGroup ρ →* IndividualGroup ρ (familyFiniteSpineWordBlock q u) s :=
  individualBase ρ (familyFiniteSpineWordBlock q u)
    (finiteSpineIndividualFillings ρ q u hrho) s

theorem finiteSpineIndividualBase_injective (s : Sx) :
    Function.Injective (finiteSpineIndividualBase ρ q u hrho s) :=
  (finiteSpineWordBlock_injective (oneRel ρ s) (q s) (u s) (hrho s)).comp
    (oneEquiv ρ s).injective

/-- The concrete map of an individual spine substitution into the simultaneous one. -/
def finiteSpineFactorToFamily (s : Sx) :
    IndividualGroup ρ (familyFiniteSpineWordBlock q u) s →*
      PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u)) :=
  factorToFamily ρ (familyFiniteSpineWordBlock q u)
    (familyFiniteSpineWordBlock_filled ρ q u hrho) s

@[simp] theorem finiteSpineFactorToFamily_mk (s : Sx)
    (w : FreeGroup (α ⊕ (Σ _ : PUnit.{1}, SpinePresentationGen (q s)))) :
    finiteSpineFactorToFamily ρ q u hrho s (QuotientGroup.mk w) =
      QuotientGroup.mk (FreeGroup.map
        (individualGenEmb (Zt := fun t => SpinePresentationGen (q t)) s) w) := rfl

/-- Every actual individual spine factor embeds, for an arbitrary family of genera. -/
theorem finiteSpineFactorToFamily_injective (s : Sx) :
    Function.Injective (finiteSpineFactorToFamily ρ q u hrho s) :=
  factorToFamily_injective ρ (familyFiniteSpineWordBlock q u)
    (familyFiniteSpineWordBlock_filled ρ q u hrho)
    (finiteSpineIndividualFillings ρ q u hrho)
    (fun t => finiteSpineWordBlock_injective (oneRel ρ t) (q t) (u t) (hrho t)) s

/-- Actual, two-sided wide-amalgam comparison for the constructed spine family. -/
def finiteSpineFamilyAmalgamEquiv :
    PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u)) ≃*
      Monoid.PushoutI (finiteSpineIndividualBase ρ q u hrho) :=
  familyAmalgamEquiv ρ (familyFiniteSpineWordBlock q u)
    (familyFiniteSpineWordBlock_filled ρ q u hrho)
    (finiteSpineIndividualFillings ρ q u hrho)

/-- The coefficient inclusion of an actual individual spine factor. -/
def finiteSpineFactorRingHom (s : Sx) :
    MonoidAlgebra ℤ (IndividualGroup ρ (familyFiniteSpineWordBlock q u) s) →+*
      MonoidAlgebra ℤ (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u))) :=
  MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineFactorToFamily ρ q u hrho s)

theorem finiteSpineFactorRingHom_injective (s : Sx) :
    Function.Injective (finiteSpineFactorRingHom ρ q u hrho s) :=
  fun _ _ h => MonoidAlgebra.coeff_injective
    (Finsupp.mapDomain_injective (finiteSpineFactorToFamily_injective ρ q u hrho s)
      (congrArg MonoidAlgebra.coeff h))

end

end FiniteChains.Davis.Genus
