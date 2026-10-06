import RequestProject.PresValidFinite
import RequestProject.OrderNerveContiguousHomotopy
import RequestProject.OrderNervePosetCoverVertexStars
import RequestProject.TopologicalSingular.MathlibComparison

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb CategoryTheory AlgebraicTopology
open scoped unitInterval
variable {α J : Type} (w : J → List (α × Bool))

noncomputable def presValidRealizationInclusion :
    C(orderNerveRealization (ValidPresPos w), orderNerveRealization (PresPos w)) :=
  ⟨orderNerveRealizationMap (Subtype.val : ValidPresPos w → PresPos w) (fun _ _ h => h),
    (orderNerveRealizationMap (Subtype.val : ValidPresPos w → PresPos w)
      (fun _ _ h => h)).hom.continuous⟩

noncomputable def presValidRealizationRetraction :
    C(orderNerveRealization (PresPos w), orderNerveRealization (ValidPresPos w)) :=
  ⟨orderNerveRealizationMap (presValidRetraction w) (presValidRetraction w).monotone,
    (orderNerveRealizationMap (presValidRetraction w) (presValidRetraction w).monotone).hom.continuous⟩

noncomputable def presValidRealizationCollapse :
    C(orderNerveRealization (PresPos w), orderNerveRealization (PresPos w)) :=
  ⟨orderNerveRealizationMap (presValidCollapse w) (presValidCollapse_monotone w),
    (orderNerveRealizationMap (presValidCollapse w) (presValidCollapse_monotone w)).hom.continuous⟩

theorem presValidRealization_section :
    (presValidRealizationRetraction w).comp (presValidRealizationInclusion w) =
      ContinuousMap.id (orderNerveRealization (ValidPresPos w)) := by
  apply ContinuousMap.ext
  intro x
  change orderNerveRealizationMap (presValidRetraction w) (presValidRetraction w).monotone
    (orderNerveRealizationMap (Subtype.val : ValidPresPos w → PresPos w) (fun _ _ h => h) x) = x
  rw [orderNerveRealizationMap_comp]
  have he : (presValidRetraction w ∘ (Subtype.val : ValidPresPos w → PresPos w)) = id :=
    funext (presValidRetraction_val w)
  simp only [he, orderNerveRealizationMap_id]

theorem presValidRealizationRetraction_inclusion (x : orderNerveRealization (ValidPresPos w)) :
    presValidRealizationRetraction w (presValidRealizationInclusion w x) = x :=
  congrArg (fun k => k x) (presValidRealization_section w)

theorem presValidRealization_inclusion_retraction :
    (presValidRealizationInclusion w).comp (presValidRealizationRetraction w) =
      presValidRealizationCollapse w := by
  apply ContinuousMap.ext
  intro x
  exact orderNerveRealizationMap_comp (presValidRetraction w) (presValidRetraction w).monotone
    (Subtype.val : ValidPresPos w → PresPos w) (fun _ _ h => h) x

theorem presValidRealizationCollapse_inclusion (x : orderNerveRealization (ValidPresPos w)) :
    presValidRealizationCollapse w (presValidRealizationInclusion w x) =
      presValidRealizationInclusion w x := by
  rw [← presValidRealization_inclusion_retraction]
  change presValidRealizationInclusion w
    (presValidRealizationRetraction w (presValidRealizationInclusion w x)) = _
  rw [presValidRealizationRetraction_inclusion]

/-- A jointly continuous deformation of the full presentation model onto its
valid-position subcomplex, in the genuine realization topology. -/
noncomputable def presValidRealizationDeformation : ContinuousMap.Homotopy
    (ContinuousMap.id (orderNerveRealization (PresPos w)))
    ((presValidRealizationInclusion w).comp (presValidRealizationRetraction w)) where
  toFun tx := orderNerveRealizationBlend id monotone_id
    (presValidCollapse w) (presValidCollapse_monotone w)
    (fun _ _ h => presValidCollapse_cross_comparable w h) tx.1 tx.2
  continuous_toFun := orderNerveRealizationBlend_continuous id monotone_id
    (presValidCollapse w) (presValidCollapse_monotone w)
    (fun _ _ h => presValidCollapse_cross_comparable w h)
  map_zero_left x := by
    rw [orderNerveRealizationBlend_zero, orderNerveRealizationMap_id]
    rfl
  map_one_left x := by
    rw [orderNerveRealizationBlend_one, presValidRealization_inclusion_retraction]
    rfl

/-- The deformation fixes the retained subcomplex pointwise at every time. -/
theorem presValidRealizationDeformation_fixed (t : I)
    (x : orderNerveRealization (ValidPresPos w)) :
    presValidRealizationDeformation w (t, presValidRealizationInclusion w x) =
      presValidRealizationInclusion w x := by
  have he : orderNerveRealizationMap id monotone_id (presValidRealizationInclusion w x) =
      orderNerveRealizationMap (presValidCollapse w) (presValidCollapse_monotone w)
        (presValidRealizationInclusion w x) := by
    rw [orderNerveRealizationMap_id]
    exact (presValidRealizationCollapse_inclusion w x).symm
  convert
    orderNerveRealizationBlend_stationary id monotone_id
      (presValidCollapse w) (presValidCollapse_monotone w)
      (fun _ _ h => presValidCollapse_cross_comparable w h) t
      (presValidRealizationInclusion w x) he using 1 <;> first | rfl | simp only [orderNerveRealizationMap_id]

/-- The full presentation model and the finite valid model have the same actual homotopy type. -/
noncomputable def presValidRealizationHomotopyEquiv : ContinuousMap.HomotopyEquiv
    (orderNerveRealization (PresPos w)) (orderNerveRealization (ValidPresPos w)) where
  toFun := presValidRealizationRetraction w
  invFun := presValidRealizationInclusion w
  left_inv := ⟨(presValidRealizationDeformation w).symm⟩
  right_inv := by rw [presValidRealization_section]

/-- This is the exact singular-homology acyclicity predicate used in Challenge. -/
theorem presValidRealization_acyclic_iff :
    Whitehead.Acyclic (orderNerveRealization (PresPos w)) ↔
      Whitehead.Acyclic (orderNerveRealization (ValidPresPos w)) :=
  Whitehead.acyclic_iff_of_homotopyEquiv (presValidRealizationHomotopyEquiv w)

noncomputable def presValidRealizationSingularHomologyIso (n : ℕ) :
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)).obj
      (orderNerveRealization (PresPos w))) ≅
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ ℤ)).obj
      (orderNerveRealization (ValidPresPos w))) :=
  TopologicalSingular.mathlibHomologyIsoOfHomotopyEquiv (presValidRealizationHomotopyEquiv w) n

end FiniteChains.PresModel
