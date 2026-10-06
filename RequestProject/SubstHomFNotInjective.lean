module

public import RequestProject.BlockFamilySubst

@[expose] public section

/-!
# The structural homomorphism of a substitution need not be injective

`FiniteChains.BlockFamily.substHomF` is the structural homomorphism of the simultaneous
substitution (3.4); `hinj` in the relative route
(`FiniteChains.BlockFox.generates_of_quotient_relative`) is its injectivity.

This file records, with a concrete example, that injectivity is **not** a consequence of the
data of the substitution together with the filling hypothesis `FilledF`: the geometric input —
that each substituted block is a surface block glued along a simply connected attaching
intersection — is genuinely needed, and therefore so is the comparison between the model of
modified chambers and the presentation complex of the substituted presentation.

The example is as small as possible.  One generator `a`, no retained relators, one replaced
entry whose relator is the empty word, and one block relator equal to `a`:

* the source presentation is `⟨a | 1⟩`, whose group is infinite cyclic;
* the substituted presentation is `⟨a | a⟩`, whose group is trivial;
* `FilledF` holds, because the replaced relator is the empty word.

Hence `substHomF` kills the class of `a` although that class is nontrivial.

`FiniteChains.BlockFamily.not_injective_substHomF_example` is the statement.  It is not a
counterexample to property (B2): it shows that the injectivity used there has to come from the
geometry of the blocks, not from the substitution data.
-/

namespace FiniteChains
namespace BlockFamily

universe u

/-- One generator. -/
abbrev exAlpha : Type u := PUnit.{u + 1}

/-- No retained relator entries. -/
abbrev exJr : Type u := PEmpty.{u + 1}

/-- One replaced relator entry. -/
abbrev exSx : Type u := PUnit.{u + 1}

/-- No internal generators in the block. -/
abbrev exZt : exSx.{u} → Type u := fun _ => PEmpty.{u + 1}

/-- One relator in the block. -/
abbrev exMt : exSx.{u} → Type u := fun _ => PUnit.{u + 1}

/-- The source presentation `⟨a | 1⟩`: the single replaced entry carries the empty word. -/
def exRho : exJr.{u} ⊕ exSx.{u} → FreeGroup exAlpha.{u} := fun _ => 1

/-- The block substituted at the replaced entry: its single relator is the generator `a`. -/
def exBsub : ∀ s : exSx.{u}, exMt.{u} s → FreeGroup (exAlpha.{u} ⊕ exZt.{u} s) :=
  fun _ _ => FreeGroup.of (Sum.inl PUnit.unit)

theorem exFilled : FilledF exRho.{u} exBsub.{u} := by
  intro s
  have h : FreeGroup.map (Sum.inl (β := Σ s : exSx.{u}, exZt.{u} s)) (exRho (Sum.inr s)) = 1 := by
    simp [exRho]
  rw [h]
  exact one_mem _

/-- The substituted presentation contains the generator `a` among its relators. -/
theorem exSubstPresF_inr :
    substPresF exRho.{u} exBsub.{u} (Sum.inr ⟨PUnit.unit, PUnit.unit⟩) =
      FreeGroup.of (Sum.inl PUnit.unit) := by
  simp [substPresF, exBsub, genEmb]

/-- The class of the generator `a` dies in the substituted presentation. -/
theorem exImage_eq_one :
    substHomF exRho.{u} exBsub.{u} exFilled
        (QuotientGroup.mk (FreeGroup.of (PUnit.unit : exAlpha.{u}))) = 1 := by
  rw [substHomF_mk]
  refine (QuotientGroup.eq_one_iff _).2 ?_
  refine Subgroup.subset_normalClosure ⟨Sum.inr ⟨PUnit.unit, PUnit.unit⟩, ?_⟩
  rw [exSubstPresF_inr]
  simp

/-- The class of the generator `a` is nontrivial in the source presentation, whose group is
infinite cyclic. -/
theorem exClass_ne_one :
    (QuotientGroup.mk (FreeGroup.of (PUnit.unit : exAlpha.{u})) :
      PresGroup exRho.{u}) ≠ 1 := by
  have hker : relSub exRho.{u} ≤ (FreeGroup.lift
      (fun _ : exAlpha.{u} => Multiplicative.ofAdd (1 : ℤ))).ker := by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨k, rfl⟩
    simp [exRho]
  set φ : PresGroup exRho.{u} →* Multiplicative ℤ :=
    QuotientGroup.lift _ (FreeGroup.lift
      (fun _ : exAlpha.{u} => Multiplicative.ofAdd (1 : ℤ))) hker with hφ
  intro hone
  have h1 : φ (QuotientGroup.mk (FreeGroup.of (PUnit.unit : exAlpha.{u}))) = 1 := by
    rw [hone, map_one]
  have h2 : φ (QuotientGroup.mk (FreeGroup.of (PUnit.unit : exAlpha.{u}))) =
      Multiplicative.ofAdd (1 : ℤ) := by
    simp [hφ]
  rw [h2] at h1
  exact absurd (Multiplicative.ofAdd.injective h1) (by decide)

/-- **The structural homomorphism of a substitution need not be injective.**  The hypothesis
`hinj` of the relative route is therefore an extra, geometric input: it cannot be derived from
the substitution data and the filling hypothesis alone. -/
theorem not_injective_substHomF_example :
    ¬ Function.Injective (substHomF exRho.{u} exBsub.{u} exFilled) := by
  intro hinj
  refine exClass_ne_one.{u} ?_
  refine hinj ?_
  rw [exImage_eq_one, map_one]

end BlockFamily
end FiniteChains
