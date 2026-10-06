import RequestProject.RelativeBlockNaturality
import RequestProject.RelativeStructuralOperation

/-! Actual rule-1 squares for shared ambient generator labels. All stage
inclusions are literal labelled presentation inclusions. Unverified source.
-/

noncomputable section
open scoped Classical

namespace FiniteChains.RelativeNormalForm

variable {A C Z S : Type} (core : C → FreeGroup A)
  (extra : S → FreeGroup (A ⊕ Z))
  {p t : S → Prop} (hpt : ∀ s, p s → t s)

def restrictedExtra (p : S → Prop) (s : {s // p s}) := extra s.val

def rawInclusion : PresMorFS (rawPresentation core (restrictedExtra extra p))
    (rawPresentation core (restrictedExtra extra t)) :=
  PresInclusionFS.mor _ _ id (oldCellIncl hpt) Function.injective_id
    (oldCellIncl_injective hpt) (by intro j; cases j <;> simp [rawPresentation, oldCellIncl,
      restrictedExtra, labelIncl])

def pairInclusion : PresMorFS (beforeCorrection core (restrictedExtra extra p))
    (beforeCorrection core (restrictedExtra extra t)) :=
  PresInclusionFS.mor _ _ id (oldCellIncl hpt) Function.injective_id
    (oldCellIncl_injective hpt) (by intro j; cases j <;> simp [beforeCorrection, oldCellIncl,
      restrictedExtra, labelIncl])

theorem ruleOne_group_square :
    (pairInclusion core extra hpt).hom.comp
      (relativeRuleOneMap core (restrictedExtra extra p)).hom =
    (relativeRuleOneMap core (restrictedExtra extra t)).hom.comp
      (rawInclusion core extra hpt).hom := by
  apply MonoidHom.ext
  intro g
  induction g using QuotientGroup.induction_on with
  | H w =>
      simp only [MonoidHom.comp_apply, relativeRuleOneMap_hom_mk]
      change QuotientGroup.mk (FreeGroup.map id (pairSubstitution w)) =
        (relativeRuleOneMap core (restrictedExtra extra t)).hom
          (QuotientGroup.mk (FreeGroup.map id w))
      simp

theorem ruleOne_chain_square
    (x : (C ⊕ {s // p s}) →₀ MonoidAlgebra ℤ
      (PresGroup (rawPresentation core (restrictedExtra extra p)))) :
    (pairInclusion core extra hpt).cells
      ((relativeRuleOneMap core (restrictedExtra extra p)).cells x) =
    (relativeRuleOneMap core (restrictedExtra extra t)).cells
      ((rawInclusion core extra hpt).cells x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [PresMorFS.cells_add, PresMorFS.cells_add, PresMorFS.cells_add,
        PresMorFS.cells_add, hx, hy]
  | single j a =>
      rw [relativeRuleOneMap_cells, Finsupp.mapRange_single]
      change Finsupp.mapDomain (oldCellIncl hpt)
        ((Finsupp.single j _).mapRange _ _) = _
      rw [Finsupp.mapRange_single, Finsupp.mapDomain_single]
      rw [relativeRuleOneMap_cells]
      change _ = (Finsupp.mapDomain (oldCellIncl hpt)
        ((Finsupp.single j a).mapRange _ _)).mapRange _ _
      rw [Finsupp.mapRange_single, Finsupp.mapDomain_single, Finsupp.mapRange_single]
      congr 1
      change MonoidAlgebra.mapDomainRingHom ℤ (pairInclusion core extra hpt).hom
          (MonoidAlgebra.mapDomainRingHom ℤ
            (relativeRuleOneMap core (restrictedExtra extra p)).hom a) =
        MonoidAlgebra.mapDomainRingHom ℤ (relativeRuleOneMap core (restrictedExtra extra t)).hom
          (MonoidAlgebra.mapDomainRingHom ℤ (rawInclusion core extra hpt).hom a)
      rw [BlockMor.mapDomainRingHom_comp', BlockMor.mapDomainRingHom_comp',
        ruleOne_group_square]

theorem ruleOne_preserves_zero
    (hzero : ∀ x, FSIsFoxCycle (rawPresentation core (restrictedExtra extra p)) x →
      (rawInclusion core extra hpt).cells x = 0)
    {x} (hx : FSIsFoxCycle (beforeCorrection core (restrictedExtra extra p)) x) :
    (pairInclusion core extra hpt).cells x = 0 :=
  fsCells_eq_zero_of_generates
    (relativeRuleOneMap core (restrictedExtra extra p))
    (relativeRuleOneMap core (restrictedExtra extra t))
    (rawInclusion core extra hpt) (pairInclusion core extra hpt)
    (ruleOne_chain_square core extra hpt) hzero
    (relativeRuleOneMap_generates core (restrictedExtra extra p)) hx

end FiniteChains.RelativeNormalForm
