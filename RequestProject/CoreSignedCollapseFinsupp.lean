module

public import RequestProject.CoreSignedCollapse
public import RequestProject.GenerationStepFinsupp
public import RequestProject.BlockFamilyBlockwiseFinsupp
public import RequestProject.ExponentCorrection

@[expose] public section

/-! Core collapse and Hurewicz reflection for arbitrary cell sets.  Only the
individual chains are finitely supported.  Core H2 vanishing is expressed by
injectivity of the genuine finitely supported exponent-sum map.
Pending Lean verification; no finiteness of the core or family is assumed. -/

noncomputable section
open scoped Classical

namespace FiniteChains

open BlockFamily

variable {A B M J : Type} [DecidableEq A] [DecidableEq B]

theorem expMatrix_augmentation (ρ : J → FreeGroup A)
    (v : J →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
    expMatrix ρ (v.mapRange (augPres ρ) (map_zero _)) =
      (coverSecondBoundary (relSub ρ) ρ v).mapRange (augPres ρ) (map_zero _) := by
  have hadd {I : Type} (x y : I →₀ MonoidAlgebra ℤ (PresGroup ρ)) :
      (x + y).mapRange (augPres ρ) (map_zero _) =
        x.mapRange (augPres ρ) (map_zero _) + y.mapRange (augPres ρ) (map_zero _) := by
    ext i : 1
    exact map_add (augPres ρ) _ _
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => rw [hadd, map_add, hv, hw, map_add, hadd]
  | single j a =>
      simp only [Finsupp.mapRange_single, expMatrix, coverSecondBoundary,
        Finsupp.linearCombination_single]
      ext i : 1
      change augPres ρ a * expVec (ρ j) i =
        augPres ρ (a * foxMatrixPres ρ i j)
      rw [map_mul, augPres_foxMatrixPres, expVec_apply]
      rfl

/-- Core rows of a supported chain on retained core cells are unchanged. -/
theorem corePres_expMatrix_retained (core : M → FreeGroup A)
    (extra : J → FreeGroup (A ⊕ B)) (c : M →₀ ℤ) (a : A) :
    expMatrix (corePres core extra) (Finsupp.mapDomain Sum.inl c) (Sum.inl a) =
      expMatrix core c a := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [Finsupp.mapDomain_add, map_add, Finsupp.add_apply, hc, hd]
  | single m n =>
      simp only [Finsupp.mapDomain_single, expMatrix, Finsupp.linearCombination_single,
        Finsupp.smul_apply, smul_eq_mul, expVec_apply]
      change n * Multiplicative.toAdd (expSum (Sum.inl a)
          (FreeGroup.map Sum.inl (core m))) =
        n * Multiplicative.toAdd (expSum a (core m))
      rw [expSum_map_inl]

/-- Injectivity on supported core chains reflects vanishing when the extra
coordinates vanish.  This is the actual H2 injection used by terminal B3. -/
theorem corePres_expMatrix_kernel_reflect (core : M → FreeGroup A)
    (extra : J → FreeGroup (A ⊕ B)) (hcore : Function.Injective (expMatrix core))
    (c : (M ⊕ J) →₀ ℤ) (hc : expMatrix (corePres core extra) c = 0)
    (hextra : ∀ j, c (Sum.inr j) = 0) : c = 0 := by
  let d := c.comapDomain Sum.inl Sum.inl_injective.injOn
  have he : Finsupp.mapDomain Sum.inl d = c := by
    apply Finsupp.mapDomain_comapDomain Sum.inl Sum.inl_injective c
    rintro (m | j) h
    · exact ⟨m, rfl⟩
    · exact False.elim ((Finsupp.mem_support_iff.mp h) (hextra j))
  have hd : expMatrix core d = 0 := by
    ext a
    rw [← corePres_expMatrix_retained core extra d a, he, hc]
    rfl
  have hz : d = 0 := hcore (hd.trans (map_zero _).symm)
  rw [← he, hz, Finsupp.mapDomain_zero]

theorem corePres_fsAugmentation_reflect (core : M → FreeGroup A)
    (extra : J → FreeGroup (A ⊕ B)) (hcore : Function.Injective (expMatrix core))
    (v : (M ⊕ J) →₀ MonoidAlgebra ℤ (PresGroup (corePres core extra)))
    (hv : FSIsFoxCycle (corePres core extra) v)
    (hextra : ∀ j, augPres (corePres core extra) (v (Sum.inr j)) = 0) :
    ∀ j, augPres (corePres core extra) (v j) = 0 := by
  let c := v.mapRange (augPres (corePres core extra)) (map_zero _)
  have hc : expMatrix (corePres core extra) c = 0 := by
    rw [expMatrix_augmentation]
    change coverSecondBoundary _ _ v = 0 at hv
    rw [hv, Finsupp.mapRange_zero]
  have hz := corePres_expMatrix_kernel_reflect core extra hcore c hc hextra
  intro j
  exact congrArg (fun c : (M ⊕ J) →₀ ℤ => c j) hz

namespace CoreSignedCollapse

variable (core : M → FreeGroup A) (extra : J → FreeGroup (A ⊕ B))
  (target : J → FreeGroup B) (rev : J → Bool)
  (hword : ∀ j, dropCore (extra j) = if rev j then (target j)⁻¹ else target j)

/-- The supported signed collapse has support contained in the extra part
of the original chain's support. -/
def cellsFS (v : (M ⊕ J) →₀ MonoidAlgebra ℤ (PresGroup (corePres core extra))) :
    J →₀ MonoidAlgebra ℤ (PresGroup target) :=
  Finsupp.onFinset (v.comapDomain Sum.inr Sum.inr_injective.injOn).support
    (fun j => if rev j then -coefficientMap core extra target rev hword (v (Sum.inr j))
      else coefficientMap core extra target rev hword (v (Sum.inr j))) (by
    intro j hj
    apply Finsupp.mem_support_iff.mpr
    intro hz
    have hz' : v (Sum.inr j) = 0 := hz
    apply hj
    simp only [hz', map_zero, neg_zero, ite_self])

omit [DecidableEq A] [DecidableEq B] in
@[simp] theorem cellsFS_apply
    (v : (M ⊕ J) →₀ MonoidAlgebra ℤ (PresGroup (corePres core extra))) (j : J) :
    cellsFS core extra target rev hword v j =
      if rev j then -coefficientMap core extra target rev hword (v (Sum.inr j))
        else coefficientMap core extra target rev hword (v (Sum.inr j)) := rfl

omit [DecidableEq A] [DecidableEq B] in
@[simp] theorem cellsFS_zero : cellsFS core extra target rev hword 0 = 0 := by
  ext j : 1
  simp [cellsFS_apply]

omit [DecidableEq A] [DecidableEq B] in
theorem cellsFS_add (v w : (M ⊕ J) →₀ MonoidAlgebra ℤ (PresGroup (corePres core extra))) :
    cellsFS core extra target rev hword (v + w) =
      cellsFS core extra target rev hword v + cellsFS core extra target rev hword w := by
  ext j : 1
  cases h : rev j <;> simp [cellsFS_apply, h, map_add, add_comm]

omit [DecidableEq A] [DecidableEq B] in
@[simp] theorem cellsFS_single_core (m : M)
    (a : MonoidAlgebra ℤ (PresGroup (corePres core extra))) :
    cellsFS core extra target rev hword (Finsupp.single (Sum.inl m) a) = 0 := by
  ext j : 1
  simp [cellsFS_apply]

omit [DecidableEq A] [DecidableEq B] in
@[simp] theorem cellsFS_single_extra (j : J)
    (a : MonoidAlgebra ℤ (PresGroup (corePres core extra))) :
    cellsFS core extra target rev hword (Finsupp.single (Sum.inr j) a) =
      Finsupp.single j (if rev j then -coefficientMap core extra target rev hword a
        else coefficientMap core extra target rev hword a) := by
  ext k : 1
  by_cases h : j = k
  · subst k
    simp [cellsFS_apply]
  · simp [cellsFS_apply, Ne.symm h]

theorem cellsFS_boundary_apply
    (v : (M ⊕ J) →₀ MonoidAlgebra ℤ (PresGroup (corePres core extra))) (b : B) :
    coverSecondBoundary (relSub target) target (cellsFS core extra target rev hword v) b =
      coefficientMap core extra target rev hword
        (coverSecondBoundary (relSub (corePres core extra)) (corePres core extra) v
          (Sum.inr b)) := by
  induction v using Finsupp.induction_linear with
  | zero => simp only [cellsFS_zero, map_zero, Finsupp.zero_apply]
  | add v w hv hw => simp only [cellsFS_add, map_add, Finsupp.add_apply, hv, hw]
  | single j a =>
      cases j with
      | inl m =>
          simp only [cellsFS_single_core, map_zero, Finsupp.zero_apply]
          rw [fsCoverSecondBoundary_apply, Finsupp.sum_single_index (zero_mul _),
            matrix_core, mul_zero, map_zero]
      | inr j =>
          simp only [cellsFS_single_extra, fsCoverSecondBoundary_apply,
            Finsupp.sum_single_index, zero_mul, map_mul, matrix_extra]
          cases rev j <;> simp

theorem cellsFS_cycle
    (v : (M ⊕ J) →₀ MonoidAlgebra ℤ (PresGroup (corePres core extra)))
    (hv : FSIsFoxCycle (corePres core extra) v) :
    FSIsFoxCycle target (cellsFS core extra target rev hword v) := by
  change coverSecondBoundary _ _ v = 0 at hv
  change coverSecondBoundary (relSub target) target (cellsFS core extra target rev hword v) = 0
  ext b : 1
  rw [cellsFS_boundary_apply, hv, Finsupp.zero_apply, map_zero]
  rfl

def morFS : PresMorFS (corePres core extra) target where
  hom := groupMap core extra target rev hword
  cells := cellsFS core extra target rev hword
  cells_add := cellsFS_add core extra target rev hword
  cells_smul := by
    intro a v
    ext j : 1
    cases h : rev j <;>
      simp [cellsFS_apply, h, Finsupp.smul_apply, smul_eq_mul, map_mul, coefficientMap]
  cells_cycle := cellsFS_cycle core extra target rev hword
  cells_aug := by
    intro v hv j
    have ha : augPres target
        (coefficientMap core extra target rev hword (v (Sum.inr j))) =
        augPres (corePres core extra) (v (Sum.inr j)) :=
      augQ_mapDomain (groupMap core extra target rev hword) _
    cases h : rev j <;> simp [cellsFS_apply, h, map_neg, ha, hv]

theorem hurewiczFS_reflect (hcore : Function.Injective (expMatrix core))
    (v : (M ⊕ J) →₀ MonoidAlgebra ℤ (PresGroup (corePres core extra)))
    (hv : FSIsFoxCycle (corePres core extra) v)
    (hz : ∀ j, augPres target (cellsFS core extra target rev hword v j) = 0) :
    ∀ j, augPres (corePres core extra) (v j) = 0 := by
  apply corePres_fsAugmentation_reflect core extra hcore v hv
  intro j
  have ha : augPres target
      (coefficientMap core extra target rev hword (v (Sum.inr j))) =
      augPres (corePres core extra) (v (Sum.inr j)) :=
    augQ_mapDomain (groupMap core extra target rev hword) _
  have h := hz j
  cases he : rev j <;> simpa [cellsFS_apply, he, map_neg, ha] using h

include hword in
theorem fsIsCockcroft (hcore : Function.Injective (expMatrix core))
    (htarget : FSIsCockcroft target) : FSIsCockcroft (corePres core extra) := by
  intro v hv
  exact hurewiczFS_reflect core extra target rev hword hcore v hv
    (htarget _ (cellsFS_cycle core extra target rev hword v hv))

end CoreSignedCollapse
end FiniteChains
