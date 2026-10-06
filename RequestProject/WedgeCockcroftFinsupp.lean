module

public import RequestProject.WedgeSigma
public import RequestProject.GenerationStepFinsupp
public import RequestProject.BlockFamilyBlockwiseFinsupp

@[expose] public section

/-! An arbitrary wedge of finite Cockcroft presentations is Cockcroft for
actual supported chains.  Retraction onto one factor reads its finite cycle
directly; no finiteness of the family or ambient alphabet is imposed.
Pending Lean verification. -/

noncomputable section
open scoped Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open BlockFamily

variable {A B J L : Type} [DecidableEq A] [DecidableEq B] [Fintype J]
  {ρ : J → FreeGroup A} {τ : L → FreeGroup B}
  {f : A → B} {g : J → L} {r : FreeGroup B →* FreeGroup A}
  (hb : IsBlock ρ τ f g r)

omit [DecidableEq A] [Fintype J] in
theorem IsBlock.retract_hom_apply (x : PresGroup ρ) : hb.retract (hb.hom x) = x := by
  induction x using QuotientGroup.induction_on with
  | H w =>
      change (QuotientGroup.mk (r (FreeGroup.map f w)) : PresGroup ρ) = QuotientGroup.mk w
      rw [hb.retract_map]

def IsBlock.retractCoefficient :
    MonoidAlgebra ℤ (PresGroup τ) →+* MonoidAlgebra ℤ (PresGroup ρ) :=
  MonoidAlgebra.mapDomainRingHom ℤ hb.retract

omit [DecidableEq A] [Fintype J] in
theorem IsBlock.retractCoefficient_ringHom (x : MonoidAlgebra ℤ (PresGroup ρ)) :
    hb.retractCoefficient (hb.ringHom x) = x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single a n =>
      change MonoidAlgebra.mapDomain hb.retract (MonoidAlgebra.mapDomain hb.hom (MonoidAlgebra.single a n)) = _
      rw [MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single, hb.retract_hom_apply]

/-- Reading a factor's coefficients through its actual retraction commutes
with the boundary at every generator in that factor. -/
theorem IsBlock.fsRetract_boundary (v : L →₀ MonoidAlgebra ℤ (PresGroup τ)) (a : A) :
    (∑ j : J, hb.retractCoefficient (v (g j)) * foxMatrixPres ρ a j) =
      hb.retractCoefficient (coverSecondBoundary (relSub τ) τ v (f a)) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw =>
      simp only [Finsupp.add_apply, map_add, add_mul, Finset.sum_add_distrib, hv, hw]
  | single l c =>
      by_cases hl : l ∈ Set.range g
      · obtain ⟨j, rfl⟩ := hl
        simp only [Finsupp.single_apply, hb.cell_injective.eq_iff,
          apply_ite hb.retractCoefficient, map_zero, ite_mul, zero_mul]
        rw [Fintype.sum_ite_eq]
        simp only [fsCoverSecondBoundary_apply, Finsupp.sum_single_index, zero_mul,
          map_mul, hb.foxMatrix_block, hb.retractCoefficient_ringHom]
      · have hn (j : J) : l ≠ g j := fun he => hl ⟨j, he.symm⟩
        have hz : foxMatrixPres τ (f a) l = 0 := by
          change quotRingHom ℤ _ (fox (f a) (τ l)) = 0
          rw [hb.fox_outside a l hl, map_zero]
        rw [fsCoverSecondBoundary_apply, Finsupp.sum_single_index (zero_mul _), hz,
          mul_zero, map_zero]
        simp [hn]

/-- The actual finitely supported ambient cycle gives a cycle of the finite
factor after applying the actual group retraction. -/
theorem IsBlock.fsRetract_cycle (v : L →₀ MonoidAlgebra ℤ (PresGroup τ))
    (hv : FSIsFoxCycle τ v) :
    IsFoxCycle ρ (fun j => hb.retractCoefficient (v (g j))) := by
  change coverSecondBoundary _ _ v = 0 at hv
  intro a
  rw [hb.fsRetract_boundary, hv, Finsupp.zero_apply, map_zero]

include hb in
theorem IsBlock.fsAugmentation_zero (hρ : IsCockcroft ρ)
    (v : L →₀ MonoidAlgebra ℤ (PresGroup τ)) (hv : FSIsFoxCycle τ v) (j : J) :
    augPres τ (v (g j)) = 0 := by
  have h := hρ _ (hb.fsRetract_cycle v hv) j
  change augPres ρ (MonoidAlgebra.mapDomainRingHom ℤ hb.retract (v (g j))) = 0 at h
  exact (augQ_mapDomain hb.retract (v (g j))).symm.trans h

variable {S : Type} {X C : S → Type} [DecidableEq S]
  [∀ s, DecidableEq (X s)] [∀ s, Fintype (C s)]

/-- The indexing family is arbitrary.  Only each individual block has a
finite cell set, as do the genuine genus spines. -/
theorem fsIsCockcroft_sigmaWedgeRel (rels : ∀ s, C s → FreeGroup (X s))
    (h : ∀ s, IsCockcroft (rels s)) : FSIsCockcroft (sigmaWedgeRel rels) := by
  intro v hv p
  obtain ⟨s, j⟩ := p
  exact (isBlock_sigmaWedge rels s).fsAugmentation_zero (h s) v hv j

end FiniteChains
