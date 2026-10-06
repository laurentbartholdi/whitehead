module

public import RequestProject.OrderNerveReturnHomotopyZero

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular
variable {P : Type} [PartialOrder P]

theorem orderReturnHomotopyNext_fill {n : ℕ} (H : OrderReturnHomotopyStage P n)
    (s : ComposableArrows P (n + 1)) :
    ∃ b : Nerve.Ch P, b ∈ Nerve.IncOn (Set.range s.obj) ∧
      Nerve.lengthProjection (n + 3) b = b ∧ Nerve.bdry b =
        orderNerveGradedEncode (n + 1) (Finsupp.single s 1) -
          orderNerveRoundTrip P (n + 1) (Finsupp.single s 1) -
            H.map (orderSimplicialBoundary P n (Finsupp.single s 1)) := by
  apply orderNerveCarriedFill s
  · exact AddSubgroup.sub_mem _
      (AddSubgroup.sub_mem _ (orderNerveGradedEncode_single_supported (n + 1) s)
        (orderNerveRoundTrip_supported (n + 1) s))
      (orderSimplicialBoundary_map_carrier H.map H.carrier s)
  · rw (config := { transparency := .default }) [map_sub, map_sub, orderNerveGradedEncode_length, H.homogeneous]
    congr 2
    exact orderSingularToNerve_length (n + 1) _
  · rw (config := { transparency := .default }) [map_sub, map_sub, ← orderNerveGradedEncode_boundary,
      orderNerveRoundTrip_boundary, H.on_boundary, sub_self]

noncomputable def orderReturnHomotopyNextMap {n : ℕ} (H : OrderReturnHomotopyStage P n) :
    (ComposableArrows P (n + 1) →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  Finsupp.linearCombination ℤ (fun s => (orderReturnHomotopyNext_fill H s).choose)

theorem orderReturnHomotopyNextMap_single {n : ℕ} (H : OrderReturnHomotopyStage P n)
    (s : ComposableArrows P (n + 1)) :
    orderReturnHomotopyNextMap H (Finsupp.single s 1) = (orderReturnHomotopyNext_fill H s).choose := by
  rw (config := { transparency := .default }) [orderReturnHomotopyNextMap, Finsupp.linearCombination_single, one_smul]

theorem orderReturnHomotopyNextMap_identity {n : ℕ} (H : OrderReturnHomotopyStage P n)
    (c : ComposableArrows P (n + 1) →₀ ℤ) :
    Nerve.bdry (orderReturnHomotopyNextMap H c) =
      orderNerveGradedEncode (n + 1) c - orderNerveRoundTrip P (n + 1) c -
        H.map (orderSimplicialBoundary P n c) := by
  let D : (ComposableArrows P (n + 1) →₀ ℤ) →ₗ[ℤ] (ComposableArrows P n →₀ ℤ) :=
    orderSimplicialBoundary P n
  have he : Nerve.bdry.toIntLinearMap.comp (orderReturnHomotopyNextMap H) =
      orderNerveGradedEncode (n + 1) - orderNerveRoundTrip P (n + 1) -
        H.map.comp D := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.sub_apply]
    change Nerve.bdry (orderReturnHomotopyNextMap H (Finsupp.single s 1)) = _
    rw (config := { transparency := .default }) [orderReturnHomotopyNextMap_single]
    exact (orderReturnHomotopyNext_fill H s).choose_spec.2.2
  exact DFunLike.congr_fun he c

noncomputable def orderReturnHomotopyStageNext {n : ℕ} (H : OrderReturnHomotopyStage P n) :
    OrderReturnHomotopyStage P (n + 1) where
  map := orderReturnHomotopyNextMap H
  carrier s := by
    rw (config := { transparency := .default }) [orderReturnHomotopyNextMap_single]
    exact (orderReturnHomotopyNext_fill H s).choose_spec.1
  homogeneous c := by
    have he : (Nerve.lengthProjection (n + 3)).toIntLinearMap.comp (orderReturnHomotopyNextMap H) =
        orderReturnHomotopyNextMap H := by
      apply Finsupp.lhom_ext'
      intro s
      apply LinearMap.ext_ring
      simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
      change Nerve.lengthProjection (n + 3) (orderReturnHomotopyNextMap H (Finsupp.single s 1)) = _
      rw (config := { transparency := .default }) [orderReturnHomotopyNextMap_single]
      exact (orderReturnHomotopyNext_fill H s).choose_spec.2.1
    exact DFunLike.congr_fun he c
  on_boundary c := by
    rw (config := { transparency := .default }) [orderReturnHomotopyNextMap_identity, orderSimplicialBoundary_squared, map_zero, sub_zero]

noncomputable def orderReturnHomotopyStage (P : Type) [PartialOrder P] :
    (n : ℕ) → OrderReturnHomotopyStage P n
  | 0 => orderReturnHomotopyStageZero
  | n + 1 => orderReturnHomotopyStageNext (orderReturnHomotopyStage P n)

noncomputable def orderReturnHomotopy (P : Type) [PartialOrder P] (n : ℕ) :
    (ComposableArrows P n →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  (orderReturnHomotopyStage P n).map

/-- Going through actual singular chains and returning to the nerve is
chain homotopic to the original simplicial chain map. -/
theorem orderReturnHomotopy_identity (n : ℕ) (c : ComposableArrows P (n + 1) →₀ ℤ) :
    Nerve.bdry (orderReturnHomotopy P (n + 1) c) =
      orderNerveGradedEncode (n + 1) c - orderNerveRoundTrip P (n + 1) c -
        orderReturnHomotopy P n (orderSimplicialBoundary P n c) :=
  orderReturnHomotopyNextMap_identity (orderReturnHomotopyStage P n) c

theorem orderReturnHomotopy_mem_inc (n : ℕ) (c : ComposableArrows P n →₀ ℤ) :
    orderReturnHomotopy P n c ∈ Nerve.Inc P :=
  orderSimplicialMap_mem_inc _ (orderReturnHomotopyStage P n).carrier c

end FiniteChains.Comb
