module

public import RequestProject.OrderNerveCellularSingularChains
public import RequestProject.OrderNerveSmallHomotopyZero
public import RequestProject.OrderNerveSmallCellularChainMap

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory TopologicalSingular SingularSubdivision

noncomputable def orderCellSingularChain0 {P : Type} [PartialOrder P] :
    (P →₀ ℤ) →ₗ[ℤ] Chain (orderNerveRealization P) 0 :=
  Finsupp.lmapDomain ℤ ℤ (fun p => orderNerveSingularSimplex (ComposableArrows.mk₀ p))

theorem orderCellSingularChain0_single {P : Type} [PartialOrder P] (p : P) (r : ℤ) :
    orderCellSingularChain0 (Finsupp.single p r) =
      Finsupp.single (orderNerveSingularSimplex (ComposableArrows.mk₀ p)) r :=
  Finsupp.mapDomain_single

/-- The realized oriented edge has its target minus its source as boundary. -/
theorem orderCellSingularChain1_boundary {P : Type} [PartialOrder P] (c : OrdEdge P →₀ ℤ) :
    boundary 0 (orderCellSingularChain1 c) = orderCellSingularChain0 (P := P) (bdry1 (orderCx P) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single e r =>
    have h0 : (nerve P).δ (0 : Fin 2) (ordEdgeNerveEquiv P e) =
        ComposableArrows.mk₀ e.val.2 := by
      apply CategoryTheory.Functor.ext (fun i => by fin_cases i; rfl)
    have h1 : (nerve P).δ (1 : Fin 2) (ordEdgeNerveEquiv P e) =
        ComposableArrows.mk₀ e.val.1 := by
      apply CategoryTheory.Functor.ext (fun i => by fin_cases i; rfl)
    rw (config := { transparency := .default }) [orderCellSingularChain1_single, boundary_single, Fin.sum_univ_two]
    simp only [orderNerveSingularSimplex_face, h0, h1, Fin.val_zero, Fin.val_one,
      pow_zero, pow_one, one_smul, neg_smul]
    rw (config := { transparency := .default }) [bdry1_single, map_smul, map_sub,
      orderCellSingularChain0_single, orderCellSingularChain0_single]
    simp [orderCx, sub_eq_add_neg]

theorem orderSmallSingularApproximation0_realization {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 0) :
    orderCellSingularChain0 (orderSmallCellularApproximation0 c) =
      orderSmallSingularApproximation0 c := by
  have he : orderCellSingularChain0.comp orderSmallCellularApproximation0 =
      (orderSmallSingularApproximation0 : smallChains (orderNerveRealizationOpenStar P) 0 →ₗ[ℤ] _) := by
    apply orderSmallSingle_spans
    intro σ
    simp only [LinearMap.comp_apply, orderSmallCellularApproximation0_single,
      orderCellSingularChain0_single, orderSmallSingularApproximation0_single]
    rfl
  exact DFunLike.congr_fun he c

end FiniteChains.Comb
