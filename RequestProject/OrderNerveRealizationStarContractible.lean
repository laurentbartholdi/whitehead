module

public import RequestProject.OrderNerveRealizationContraction
public import RequestProject.OrderNerveRealizationStarSheets
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory

/-- Closed vertex-star carriers are contractible in the actual CW topology. -/
theorem orderNerveRealization_closedStar_contractible {P : Type} [PartialOrder P] (v : P) :
    ContractibleSpace (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v) :
      Set (orderNerveRealization P)) := by
  let a : orderNerveVertexStar P v := ⟨v, Or.inl le_rfl⟩
  letI := orderNerveRealization_contractible_of_comparable a (fun p => p.property)
  exact (orderNerveRealizationSubtypeHomeomorph (orderNerveVertexStar P v)).symm.contractibleSpace

/-- Passing to the comparable-vertex subposet preserves the actual open star. -/
noncomputable def orderNerveRealizationOpenStar_subtypeHomeomorph {P : Type}
    [PartialOrder P] (v : P) :
    orderNerveRealizationOpenStar (orderNerveVertexStar P v) ⟨v, Or.inl le_rfl⟩ ≃ₜ
      orderNerveRealizationOpenStar P v :=
  ((orderNerveRealizationSubtypeHomeomorph (orderNerveVertexStar P v)).subtype
    (p := fun x => x ∈ orderNerveRealizationOpenStar (orderNerveVertexStar P v)
      ⟨v, Or.inl le_rfl⟩)
    (q := fun x => x.val ∈ orderNerveRealizationOpenStar P v) (by
      intro x
      change (0 < orderNerveRealizationCoordinates (orderNerveVertexStar P v) x
        ⟨v, Or.inl le_rfl⟩) ↔
        (0 < orderNerveRealizationCoordinates P
          (orderNerveRealizationSubtypeHomeomorph (orderNerveVertexStar P v) x).val v)
      rw [orderNerveRealizationSubtypeHomeomorph_coe]
      exact (congrArg (fun r : ℝ => 0 < r)
        (orderNerveRealizationCoordinates_map_injective
          (Subtype.val : orderNerveVertexStar P v → P) (fun _ _ h => h)
          Subtype.val_injective x ⟨v, Or.inl le_rfl⟩)).symm.to_iff)).trans
    (orderNerveNestedCarrierHomeomorph _ _
      (orderNerveRealizationOpenStar_subset_subcomplex v)).symm

/-- Every open vertex star is contractible, including in an infinite poset nerve. -/
theorem orderNerveRealizationOpenStar_contractible {P : Type} [PartialOrder P] (v : P) :
    ContractibleSpace (orderNerveRealizationOpenStar P v) := by
  let a : orderNerveVertexStar P v := ⟨v, Or.inl le_rfl⟩
  letI := orderNerveRealizationOpenStar_contractible_of_comparable a (fun p => p.property)
  exact (orderNerveRealizationOpenStar_subtypeHomeomorph v).symm.contractibleSpace

/-- The canonical open vertex stars are simply connected open neighborhoods. -/
theorem orderNerveRealizationOpenStar_simplyConnected {P : Type} [PartialOrder P] (v : P) :
    IsSimplyConnected (orderNerveRealizationOpenStar P v) := by
  letI := orderNerveRealizationOpenStar_contractible v
  exact inferInstanceAs (SimplyConnectedSpace (orderNerveRealizationOpenStar P v))

end FiniteChains.Comb
