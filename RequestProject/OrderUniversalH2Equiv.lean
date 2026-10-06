import RequestProject.OrderNerveH2
import RequestProject.PresUniversalRelatorKernel

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

/-- The actual lifted-order/path-class cover comparison on two-cycles. -/
noncomputable def uOrderCycleEquiv :
    LinearMap.ker (FiniteChains.Comb.bdry2 (orderCx (UOrder P a))) ≃ₗ[ℤ]
      LinearMap.ker (bdry2 (uCover (orderCx P) a)) where
  toFun c := ⟨uOrderChain2Equiv c.val, (uOrderHom_cycle_iff c.val).mpr c.property⟩
  invFun c := ⟨uOrderChain2Equiv.symm c.val, by
    apply (uOrderHom_cycle_iff _).mp
    change bdry2 (uCover (orderCx P) a)
      (uOrderChain2Equiv (uOrderChain2Equiv.symm c.val)) = 0
    rw (config := { transparency := .default }) [uOrderChain2Equiv.apply_symm_apply]; exact c.property⟩
  left_inv c := Subtype.ext (uOrderChain2Equiv.symm_apply_apply c.val)
  right_inv c := Subtype.ext (uOrderChain2Equiv.apply_symm_apply c.val)
  map_add' c d := Subtype.ext (map_add _ _ _)
  map_smul' n c := Subtype.ext (map_smul _ _ _)

/-- The actual comparison identifies exactly the genuine three-boundary submodules. -/
theorem uOrderCycleEquiv_boundary_range :
    (LinearMap.range (ordBoundary3Cycles (UOrder P a))).map
      uOrderCycleEquiv.toLinearMap = LinearMap.range (uOrdBoundary3Cycles (P := P) (a := a)) := by
  ext c
  constructor
  · rintro ⟨d, ⟨y, rfl⟩, rfl⟩
    exact ⟨Finsupp.mapDomain uOrderTet y,
      Subtype.ext (uOrderHom_ordBoundary3 y).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨d, hd⟩ := exists_uOrder_three_chain y
    refine ⟨ordBoundary3Cycles (UOrder P a) d, ⟨d, rfl⟩, ?_⟩
    apply Subtype.ext
    change chain2 uOrderHom (ordBoundary3 d) = uOrdBoundary3 y
    rw (config := { transparency := .default }) [uOrderHom_ordBoundary3, hd]

/-- The genuine second homology quotients of the two actual universal-cover models agree. -/
noncomputable def uOrderH2Equiv : OrderNerveH2 (UOrder P a) ≃ₗ[ℤ]
    (LinearMap.ker (bdry2 (uCover (orderCx P) a))) ⧸
      LinearMap.range (uOrdBoundary3Cycles (P := P) (a := a)) :=
  Submodule.Quotient.equiv _ _ uOrderCycleEquiv uOrderCycleEquiv_boundary_range

end FiniteChains.Comb
