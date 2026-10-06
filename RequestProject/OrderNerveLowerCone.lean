import RequestProject.OrderNerveConeBall
import RequestProject.OrderNervePosetCoverVertexStars
import RequestProject.PosetCoverLowerInterval

/-! A closed principal lower ideal is literally the order cone on its strict
lower interval. The realized identification respects the boundary inclusion. -/

noncomputable section
namespace FiniteChains.Comb
open scoped Classical

variable {P Q : Type} [PartialOrder P] [PartialOrder Q] (v : Q)
    (e : P ≃o StrictBelow v)

def lowerConeMap : WithTop P → Set.Iic v := WithTop.recTopCoe
  ⟨v, le_rfl⟩ (fun p => ⟨(e p).val, (e p).property.le⟩)

@[simp] theorem lowerConeMap_top : lowerConeMap v e ⊤ = ⟨v, le_rfl⟩ := rfl
@[simp] theorem lowerConeMap_coe (p : P) :
    lowerConeMap v e (p : WithTop P) = ⟨(e p).val, (e p).property.le⟩ := rfl

theorem lowerConeMap_bijective : Function.Bijective (lowerConeMap v e) := by
  constructor
  · intro a b h
    induction a using WithTop.recTopCoe with
    | top =>
        induction b using WithTop.recTopCoe with
        | top => rfl
        | coe b => exact ((ne_of_lt (e b).property)
            (congrArg Subtype.val h).symm).elim
    | coe a =>
        induction b using WithTop.recTopCoe with
        | top => exact ((ne_of_lt (e a).property) (congrArg Subtype.val h)).elim
        | coe b =>
            exact congrArg (fun p : P => (p : WithTop P))
              (e.injective (Subtype.ext (congrArg (fun y : Set.Iic v => y.val) h)))
  · intro x
    by_cases hx : x.val = v
    · exact ⟨⊤, Subtype.ext hx.symm⟩
    · let p : StrictBelow v := ⟨x.val, lt_of_le_of_ne x.property hx⟩
      exact ⟨(e.symm p : WithTop P), Subtype.ext
        (congrArg (fun y : StrictBelow v => y.val) (e.apply_symm_apply p))⟩

def lowerConeOrderIso : WithTop P ≃o Set.Iic v where
  toEquiv := Equiv.ofBijective (lowerConeMap v e) (lowerConeMap_bijective v e)
  map_rel_iff' := by
    intro a b
    induction a using WithTop.recTopCoe with
    | top =>
        induction b using WithTop.recTopCoe with
        | top => exact iff_of_true le_rfl le_rfl
        | coe b =>
            change v ≤ (e b).val ↔ (⊤ : WithTop P) ≤ b
            exact iff_of_false (not_le_of_gt (e b).property) (not_le_of_gt (WithTop.coe_lt_top b))
    | coe a =>
        induction b using WithTop.recTopCoe with
        | top => exact iff_of_true (e a).property.le le_top
        | coe b =>
            change (e a).val ≤ (e b).val ↔ (a : WithTop P) ≤ b
            exact e.map_rel_iff.trans WithTop.coe_le_coe.symm

def lowerConeBoundary : P →o Set.Iic v where
  toFun p := ⟨(e p).val, (e p).property.le⟩
  monotone' := fun _ _ h => e.monotone h

theorem lowerConeRealization_boundary (x : orderNerveRealization P) :
    orderNerveRealizationOrderIso (lowerConeOrderIso v e) (orderNerveConeBase P x) =
      orderNerveRealizationMap (lowerConeBoundary v e) (lowerConeBoundary v e).monotone x := by
  change orderNerveRealizationMap (lowerConeOrderIso v e) (lowerConeOrderIso v e).monotone
      (orderNerveRealizationMap (fun p : P => (p : WithTop P)) WithTop.coe_mono x) = _
  rw [orderNerveRealizationMap_comp]
  rfl

variable [Fintype P] [Nonempty P]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (b : orderNerveRealization P ≃ₜ RelativeAttachment.UnitBoundary E)

def lowerConeBallHomeomorph :
    orderNerveRealization (Set.Iic v) ≃ₜ RelativeAttachment.ClosedUnitBall E :=
  (orderNerveRealizationOrderIso (lowerConeOrderIso v e)).symm.trans
    (orderNerveWithTopBallHomeomorph b)

theorem lowerConeBallHomeomorph_boundary (x : orderNerveRealization P) :
    lowerConeBallHomeomorph v e b
      (orderNerveRealizationMap (lowerConeBoundary v e) (lowerConeBoundary v e).monotone x) =
      RelativeAttachment.unitBoundaryInclusion E (b x) := by
  rw [← lowerConeRealization_boundary]
  change orderNerveWithTopBallHomeomorph b
      ((orderNerveRealizationOrderIso (lowerConeOrderIso v e)).symm
        (orderNerveRealizationOrderIso (lowerConeOrderIso v e) (orderNerveConeBase P x))) = _
  rw [Homeomorph.symm_apply_apply, orderNerveWithTopBallHomeomorph_boundary]

theorem lowerConeBallHomeomorph_boundary_iff (x : orderNerveRealization (Set.Iic v)) :
    ‖(lowerConeBallHomeomorph v e b x).val‖ = 1 ↔
      x ∈ Set.range (orderNerveRealizationMap
        (lowerConeBoundary v e) (lowerConeBoundary v e).monotone) := by
  change ‖(orderNerveWithTopBallHomeomorph b
    ((orderNerveRealizationOrderIso (lowerConeOrderIso v e)).symm x)).val‖ = 1 ↔ _
  rw [orderNerveWithTopBallHomeomorph_boundary_iff]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, (lowerConeRealization_boundary v e u).symm.trans
      ((congrArg (orderNerveRealizationOrderIso (lowerConeOrderIso v e)) hu).trans
        (Homeomorph.apply_symm_apply _ x))⟩
  · rintro ⟨u, rfl⟩
    refine ⟨u, ?_⟩
    rw [← lowerConeRealization_boundary, Homeomorph.symm_apply_apply]

end FiniteChains.Comb
