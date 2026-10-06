module

public import RequestProject.PresCoverRelatorKernelEquiv
public import RequestProject.PresUniversalRelatorKernel

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool))
  (hpos : ∀ j, 0 < (w j).length)

/-- The actual path-class cycle-coordinate range is exactly the actual collapsed-boundary kernel. -/
theorem presUniversalCycleRelatorCoordinates_range :
    LinearMap.range (presUniversalCycleRelatorCoordinates w hpos) =
      LinearMap.ker (presCoverCollapsedRelatorBoundary w uOrderEnd
        (presUniversalEnd_isPosetCover w hpos)) := by
  ext c
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨d, rfl⟩
    exact presCover_cycle_collapsed_relator_boundary_zero w uOrderEnd
      (presUniversalEnd_isPosetCover w hpos) hpos (uOrderNormalizeChain2 d.val)
      (uOrderNormalizeChain2_cycle d.val (LinearMap.mem_ker.mp d.property))
  · intro hc
    obtain ⟨z, hz, he⟩ := exists_presCover_cycle_of_collapsed_relator_boundary w uOrderEnd
      (presUniversalEnd_isPosetCover w hpos) hpos c hc
    let b := Finsupp.mapDomain (strictOrderIncl (UOrder (PresPos w) (ptBase w))).onF z
    let u := uOrderChain2Equiv b
    have hb : Comb.bdry2 (orderCx (UOrder (PresPos w) (ptBase w))) b = 0 :=
      (bdry2_chain2 (strictOrderIncl _) z).trans (by rw [hz, map_zero])
    have hu : Comb.bdry2 (uCover (orderCx (PresPos w)) (ptBase w)) u = 0 :=
      (uOrderHom_cycle_iff b).mpr hb
    refine ⟨⟨u, LinearMap.mem_ker.mpr hu⟩, ?_⟩
    exact (presUniversalRelatorCoordinates_inclusion w hpos z).trans he

/-- Genuine universal-cover cycle classes are linearly equivalent to the actual
collapsed relator-boundary kernel, without any assumed Fox or Hurewicz comparison. -/
noncomputable def presUniversalCycleQuotientCollapsedKernelEquiv :
    (LinearMap.ker (Comb.bdry2 (uCover (orderCx (PresPos w)) (ptBase w))) ⧸
      LinearMap.range (uOrdBoundary3Cycles (P := PresPos w) (a := ptBase w))) ≃ₗ[ℤ]
        LinearMap.ker (presCoverCollapsedRelatorBoundary w uOrderEnd
          (presUniversalEnd_isPosetCover w hpos)) :=
  (presUniversalCycleQuotientRelatorEquiv w hpos).trans
    (LinearEquiv.ofEq _ _ (presUniversalCycleRelatorCoordinates_range w hpos))

theorem presUniversalCycleQuotientCollapsedKernelEquiv_mk
    (c : LinearMap.ker (Comb.bdry2 (uCover (orderCx (PresPos w)) (ptBase w)))) :
    (presUniversalCycleQuotientCollapsedKernelEquiv w hpos (Submodule.Quotient.mk c)).val =
      presUniversalRelatorCoordinates w hpos c.val :=
  presUniversalCycleQuotientRelatorEquiv_mk w hpos c

end FiniteChains.PresModel
