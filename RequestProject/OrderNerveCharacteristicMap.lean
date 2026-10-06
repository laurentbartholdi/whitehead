module

public import RequestProject.OrderNerveClosedBallChart
public import Mathlib.Logic.Equiv.PartialEquiv

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped Classical

/-- Extend the genuine closed-ball chart to an ambient function, using its centre
value outside the closed ball. Only its closed-ball restriction is characteristic data. -/
noncomputable def orderNerveCharacteristicFunction {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) (x : Fin n → ℝ) : orderNerveRealization P :=
  if hx : x ∈ Metric.closedBall 0 1 then orderNerveClosedBallChart s ⟨x, hx⟩
  else orderNerveClosedBallChart s ⟨0, Metric.mem_closedBall_self (by norm_num)⟩

 theorem orderNerveCharacteristicFunction_closedBall {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) (x : (Metric.closedBall 0 1 : Set (Fin n → ℝ))) :
    orderNerveCharacteristicFunction s x.val = orderNerveClosedBallChart s x := by
  simp [orderNerveCharacteristicFunction, x.property]

 theorem orderNerveCharacteristicFunction_continuousOn {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) :
    ContinuousOn (orderNerveCharacteristicFunction s) (Metric.closedBall 0 1) := by
  apply continuousOn_iff_continuous_restrict.mpr
  have h : (Metric.closedBall 0 1 : Set (Fin n → ℝ)).domRestrict
      (orderNerveCharacteristicFunction s) = orderNerveClosedBallChart s := by
    funext x
    exact orderNerveCharacteristicFunction_closedBall s x
  rw (config := { transparency := .default }) [h]
  exact (orderNerveClosedBallChart s).continuous

 theorem orderNerveCharacteristicFunction_injOn {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) :
    Set.InjOn (orderNerveCharacteristicFunction s) (Metric.ball 0 1) := by
  intro x hx y hy h
  have hx' := Metric.ball_subset_closedBall hx
  have hy' := Metric.ball_subset_closedBall hy
  have hc : orderNerveClosedBallChart s ⟨x, hx'⟩ = orderNerveClosedBallChart s ⟨y, hy'⟩ := by
    simpa only [orderNerveCharacteristicFunction_closedBall s ⟨x, hx'⟩,
      orderNerveCharacteristicFunction_closedBall s ⟨y, hy'⟩] using h
  exact congrArg Subtype.val (orderNerveClosedBallChart_injective s hc)

/-- The genuine realization characteristic map as a PartialEquiv with open-ball source. -/
noncomputable def orderNerveCharacteristicMap {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) : PartialEquiv (Fin n → ℝ) (orderNerveRealization P) :=
  (orderNerveCharacteristicFunction_injOn s).toPartialEquiv
    (orderNerveCharacteristicFunction s) (Metric.ball 0 1)

 theorem orderNerveCharacteristicMap_source {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) :
    (orderNerveCharacteristicMap s).source = Metric.ball 0 1 := rfl

 theorem orderNerveCharacteristicMap_continuousOn {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) :
    ContinuousOn (orderNerveCharacteristicMap s) (Metric.closedBall 0 1) :=
  orderNerveCharacteristicFunction_continuousOn s

/-- The inverse characteristic map is continuous on its actual open-cell target. -/
theorem orderNerveCharacteristicMap_continuousOn_symm {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) :
    ContinuousOn (orderNerveCharacteristicMap s).symm (orderNerveCharacteristicMap s).target := by
  let e := orderNerveCharacteristicMap s
  let g : e.target → (Metric.closedBall 0 1 : Set (Fin n → ℝ)) := fun x =>
    ⟨e.symm x.val, Metric.ball_subset_closedBall (by
      have h := e.map_target x.property
      change e.symm x.val ∈ Metric.ball 0 1 at h
      exact h)⟩
  have hc : Topology.IsEmbedding (orderNerveClosedBallChart s) :=
    ((orderNerveClosedBallChart s).continuous.isClosedEmbedding
      (orderNerveClosedBallChart_injective s)).isEmbedding
  have hg : Continuous g := by
    apply hc.isInducing.continuous_iff.mpr
    have he : orderNerveClosedBallChart s ∘ g = (Subtype.val : e.target → orderNerveRealization P) := by
      funext x
      have h := orderNerveCharacteristicFunction_closedBall s (g x)
      change e (e.symm x.val) = orderNerveClosedBallChart s (g x) at h
      exact h.symm.trans (e.right_inv x.property)
    rw (config := { transparency := .default }) [he]
    exact continuous_subtype_val
  apply continuousOn_iff_continuous_restrict.mpr
  exact continuous_subtype_val.comp hg

end FiniteChains.Comb
