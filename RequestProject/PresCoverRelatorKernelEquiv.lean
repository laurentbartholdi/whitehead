module

public import RequestProject.PresCoverRelatorCycleRealization

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f) (hpos : ∀ j, 0 < (w j).length)

/-- The genuine collapsed attaching-boundary linear map on actual finite lifted relators. -/
noncomputable def presCoverCollapsedRelatorBoundary :
    (PresCoverRelator w f →₀ ℤ) →ₗ[ℤ]
      (StrictOrdEdge {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ) :=
  (normalizedStrictChain1 (presCoverCylinderCollapse w f hf)
    (presCoverCylinderCollapse_monotone w f hf)).comp
      (presCoverCylinderRelatorBoundaryChain w f hf)

/-- Actual genuine two-cycle coordinates take values in the proved collapsed-boundary kernel. -/
noncomputable def presCoverCycleRelatorKernelMap :
    LinearMap.ker (Comb.bdry2 (strictOrderCx P)) →ₗ[ℤ]
      LinearMap.ker (presCoverCollapsedRelatorBoundary w f hf) :=
  (presCoverCycleRelatorLinear w f hf hpos).codRestrict
    (LinearMap.ker (presCoverCollapsedRelatorBoundary w f hf))
    (fun c => LinearMap.mem_ker.mpr
      (presCover_cycle_collapsed_relator_boundary_zero w f hf hpos c.val
        (LinearMap.mem_ker.mp c.property)))

theorem presCoverCycleRelatorKernelMap_injective :
    Function.Injective (presCoverCycleRelatorKernelMap w f hf hpos) := by
  intro c d he
  apply presCoverCycleRelatorLinear_injective w f hf hpos
  exact congrArg Subtype.val he

theorem presCoverCycleRelatorKernelMap_surjective :
    Function.Surjective (presCoverCycleRelatorKernelMap w f hf hpos) := by
  intro c
  obtain ⟨z, hz, he⟩ := exists_presCover_cycle_of_collapsed_relator_boundary w f hf hpos c.val
    (LinearMap.mem_ker.mp c.property)
  exact ⟨⟨z, LinearMap.mem_ker.mpr hz⟩, Subtype.ext he⟩

/-- Genuine presentation-cover two-cycles are linearly equivalent to the kernel of
its actual collapsed attaching-boundary map, with no assumed comparison premise. -/
noncomputable def presCoverCycleRelatorKernelEquiv :
    LinearMap.ker (Comb.bdry2 (strictOrderCx P)) ≃ₗ[ℤ]
      LinearMap.ker (presCoverCollapsedRelatorBoundary w f hf) :=
  LinearEquiv.ofBijective (presCoverCycleRelatorKernelMap w f hf hpos)
    ⟨presCoverCycleRelatorKernelMap_injective w f hf hpos,
      presCoverCycleRelatorKernelMap_surjective w f hf hpos⟩

theorem presCoverCycleRelatorKernelEquiv_apply
    (c : LinearMap.ker (Comb.bdry2 (strictOrderCx P))) :
    (presCoverCycleRelatorKernelEquiv w f hf hpos c).val =
      presCoverRelatorChain w f hf hpos c.val := rfl

end FiniteChains.PresModel
