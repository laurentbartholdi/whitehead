import RequestProject.CoreCollapse
import RequestProject.FoxCoordinateSubstitution

/-! The actual core-collapse map, including reversed orientations of surviving cells.
The only input describing the quotient is an equality of free-group words.  The
group map, signed cellular map and Hurewicz reflection are constructed below.
Written proof terms; not compiled in the current proof-first workflow. -/

noncomputable section
open scoped Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.CoreSignedCollapse

variable {A B M J : Type}

/-- Collapse the core generators and retain each extra generator. -/
def dropCore : FreeGroup (A ⊕ B) →* FreeGroup B :=
  FreeGroup.lift (Sum.elim (fun _ => 1) FreeGroup.of)

@[simp] theorem dropCore_of_inl (a : A) :
    dropCore (B := B) (FreeGroup.of (Sum.inl a)) = 1 := by
  simp [dropCore]

@[simp] theorem dropCore_of_inr (b : B) :
    dropCore (A := A) (FreeGroup.of (Sum.inr b)) = FreeGroup.of b := by
  simp [dropCore]

@[simp] theorem dropCore_map_inl (w : FreeGroup A) :
    dropCore (B := B) (FreeGroup.map Sum.inl w) = 1 := by
  have h : (dropCore (A := A) (B := B)).comp (FreeGroup.map Sum.inl) = 1 := by
    apply FreeGroup.ext_hom
    intro a
    simp
  exact DFunLike.congr_fun h w

@[simp] theorem dropCore_map_inr (w : FreeGroup B) :
    dropCore (A := A) (FreeGroup.map Sum.inr w) = w := by
  have h : (dropCore (A := A) (B := B)).comp (FreeGroup.map Sum.inr) =
      MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro b
    simp
  exact DFunLike.congr_fun h w

variable (core : M → FreeGroup A) (extra : J → FreeGroup (A ⊕ B))
  (target : J → FreeGroup B) (rev : J → Bool)
  (hword : ∀ j, dropCore (extra j) = if rev j then (target j)⁻¹ else target j)

/-- The collapse descends because every collapsed attaching word is a target
relator or its inverse. -/
def groupMap : PresGroup (corePres core extra) →* PresGroup target :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (relSub target)).comp dropCore) (by
      refine Subgroup.normalClosure_le_normal ?_
      rintro _ ⟨m | j, rfl⟩
      · change (QuotientGroup.mk' (relSub target))
          (dropCore (FreeGroup.map Sum.inl (core m))) = 1
        rw [dropCore_map_inl, map_one]
      · change (QuotientGroup.mk' (relSub target)) (dropCore (extra j)) = 1
        have ht : (QuotientGroup.mk (target j) : PresGroup target) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr
            (Subgroup.subset_normalClosure ⟨j, rfl⟩)
        rw [hword j]
        cases rev j <;> simp [ht])

def coefficientMap : MonoidAlgebra ℤ (PresGroup (corePres core extra)) →+*
    MonoidAlgebra ℤ (PresGroup target) :=
  MonoidAlgebra.mapDomainRingHom ℤ (groupMap core extra target rev hword)

theorem coefficientMap_quot (x : FreeGroupRing (A ⊕ B)) :
    coefficientMap core extra target rev hword
      (quotRingHom ℤ (relSub (corePres core extra)) x) =
    quotRingHom ℤ (relSub target)
      (MonoidAlgebra.mapDomainRingHom ℤ dropCore x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single g n =>
      change MonoidAlgebra.mapDomain _ (MonoidAlgebra.mapDomain _ (MonoidAlgebra.single g n)) =
        MonoidAlgebra.mapDomain _ (MonoidAlgebra.mapDomain _ (MonoidAlgebra.single g n))
      simp only [MonoidAlgebra.mapDomain_single]
      rfl

variable [DecidableEq A] [DecidableEq B]

theorem coefficientMap_fox (b : B) (w : FreeGroup (A ⊕ B)) :
    coefficientMap core extra target rev hword
      (quotRingHom ℤ (relSub (corePres core extra)) (fox (Sum.inr b) w)) =
    quotRingHom ℤ (relSub target) (fox b (dropCore w)) := by
  rw [coefficientMap_quot]
  congr 1
  symm
  apply fox_subst_coordinate
  rintro (a | b') <;> simp [fox_of]

theorem quotientFox_inv_relator (b : B) (j : J) :
    quotRingHom ℤ (relSub target) (fox b (target j)⁻¹) =
      -foxMatrixPres target b j := by
  have ht : (QuotientGroup.mk ((target j)⁻¹) : PresGroup target) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact inv_mem (Subgroup.subset_normalClosure ⟨j, rfl⟩)
  have hg : quotRingHom ℤ (relSub target) (grp (target j)⁻¹) = 1 := by
    change quotRingHom ℤ _ (MonoidAlgebra.single _ 1) = _
    rw [quotRingHom_single, ht]
    rfl
  rw [fox_inv, map_neg, map_mul, hg, one_mul]
  rfl

theorem matrix_core (b : B) (m : M) :
    foxMatrixPres (corePres core extra) (Sum.inr b) (Sum.inl m) = 0 := by
  change quotRingHom ℤ _ (fox (Sum.inr b) (FreeGroup.map Sum.inl (core m))) = 0
  rw [fox_map_of_not_mem_range Sum.inl (fun _ => Sum.inr_ne_inl), map_zero]

theorem matrix_extra (b : B) (j : J) :
    coefficientMap core extra target rev hword
      (foxMatrixPres (corePres core extra) (Sum.inr b) (Sum.inr j)) =
      if rev j then -foxMatrixPres target b j else foxMatrixPres target b j := by
  change coefficientMap core extra target rev hword
    (quotRingHom ℤ _ (fox (Sum.inr b) (extra j))) = _
  rw [coefficientMap_fox, hword j]
  cases h : rev j
  · rfl
  · exact quotientFox_inv_relator target b j

/-- The cellular collapse discards the core and records the actual orientation
of each surviving two-cell. -/
def cells (v : M ⊕ J → MonoidAlgebra ℤ (PresGroup (corePres core extra))) :
    J → MonoidAlgebra ℤ (PresGroup target) :=
  fun j => if rev j then -coefficientMap core extra target rev hword (v (Sum.inr j))
    else coefficientMap core extra target rev hword (v (Sum.inr j))

variable [Fintype M] [Fintype J]

theorem cells_cycle
    (v : M ⊕ J → MonoidAlgebra ℤ (PresGroup (corePres core extra)))
    (hv : IsFoxCycle (corePres core extra) v) :
    IsFoxCycle target (cells core extra target rev hword v) := by
  intro b
  have h := congrArg (coefficientMap core extra target rev hword) (hv (Sum.inr b))
  rw [Fintype.sum_sum_type] at h
  simp only [matrix_core, mul_zero, Finset.sum_const_zero, zero_add,
    map_sum, map_mul, matrix_extra, map_zero] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro j hj
  cases he : rev j <;> simp [cells, he]

/-- A structural map with no assumed chain-map or Hurewicz property. -/
def mor : PresMor (corePres core extra) target where
  hom := groupMap core extra target rev hword
  cells := cells core extra target rev hword
  cells_add := by
    intro v w
    funext j
    cases h : rev j <;> simp [cells, h, map_add, add_comm]
  cells_smul := by
    intro a v
    funext j
    cases h : rev j <;>
      simp [cells, h, Pi.smul_apply, smul_eq_mul, map_mul, coefficientMap]
  cells_cycle := cells_cycle core extra target rev hword
  cells_aug := by
    intro v hv j
    have ha : augPres target
        (coefficientMap core extra target rev hword (v (Sum.inr j))) =
        augPres (corePres core extra) (v (Sum.inr j)) :=
      augQ_mapDomain (groupMap core extra target rev hword) _
    cases h : rev j <;> simp [cells, h, map_neg, ha, hv]

/-- The collapse is injective on Hurewicz images of Fox cycles: first undo each
orientation sign, then use the exponent-sum injection of the core. -/
theorem hurewicz_reflect (hcore : ExpInjective core)
    (v : M ⊕ J → MonoidAlgebra ℤ (PresGroup (corePres core extra)))
    (hv : IsFoxCycle (corePres core extra) v)
    (hz : ∀ j, augPres target (cells core extra target rev hword v j) = 0) :
    ∀ j, augPres (corePres core extra) (v j) = 0 := by
  apply augPres_eq_zero_of_extra core extra hcore hv
  intro j
  have ha : augPres target
      (coefficientMap core extra target rev hword (v (Sum.inr j))) =
      augPres (corePres core extra) (v (Sum.inr j)) :=
    augQ_mapDomain (groupMap core extra target rev hword) _
  have hh := hz j
  cases h : rev j <;> simpa [cells, h, map_neg, ha] using hh

include hword in
theorem isCockcroft (hcore : ExpInjective core) (htarget : IsCockcroft target) :
    IsCockcroft (corePres core extra) := by
  intro v hv
  exact hurewicz_reflect core extra target rev hword hcore v hv
    (htarget _ (cells_cycle core extra target rev hword v hv))

end FiniteChains.CoreSignedCollapse
