import RequestProject.TopologicalCoverPullbackHomotopy
import RequestProject.TopologicalSingular.MathlibComparison

/-! Homotopy invariance of the acyclic regular covering condition in the
original statement. The covering is the concrete pullback, and its total
space is compared with the original total space by the actual projection. -/

noncomputable section
namespace Whitehead
open scoped Topology unitInterval

theorem connectedSpace_of_homotopyEquiv {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [ConnectedSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) : ConnectedSpace X := by
  let y₀ : Y := Classical.choice inferInstance
  let H := Classical.choice e.left_inv
  apply connectedSpace_iff_connectedComponent.mpr
  refine ⟨e.invFun y₀, Set.eq_univ_of_forall fun x => ?_⟩
  have hi : e.invFun (e.toFun x) ∈ connectedComponent (e.invFun y₀) :=
    (isConnected_range e.invFun.continuous).subset_connectedComponent
      ⟨y₀, rfl⟩ ⟨e.toFun x, rfl⟩
  have hc : Continuous (fun t : I => H (t, x)) :=
    H.continuous.comp (continuous_id.prodMk continuous_const)
  have hx : x ∈ connectedComponent (e.invFun (e.toFun x)) :=
    (isConnected_range hc).subset_connectedComponent
      ⟨0, H.apply_zero x⟩ ⟨1, H.apply_one x⟩
  rw [connectedComponent_eq hi]
  exact hx

theorem connectedSpace_homotopyEquiv_iff {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) : ConnectedSpace X ↔ ConnectedSpace Y := by
  constructor
  · intro h
    letI := h
    exact connectedSpace_of_homotopyEquiv e.symm
  · intro h
    letI := h
    exact connectedSpace_of_homotopyEquiv e

/-- Pull an actual connected acyclic regular covering back along a homotopy
equivalence of the bases. No local connectedness or CW structure is needed
on the total space of the given covering. -/
theorem hasAcyclicRegularCover_of_homotopyEquiv (K L : TwoComplex)
    (e : ContinuousMap.HomotopyEquiv K L) (h : HasAcyclicRegularCover L) :
    HasAcyclicRegularCover K := by
  obtain ⟨D, tD, p, hp, hsurj, hconn, hreg, hac⟩ := h
  letI : TopologicalSpace D := tD
  letI : ConnectedSpace D := hconn
  let P := CoverPullback e.toFun p
  let E := coverPullbackMapHomotopyEquiv e p hp
  refine ⟨P, inferInstance, coverPullbackProjection e.toFun p,
    coverPullbackProjection_isCoveringMap e.toFun p hp,
    coverPullbackProjection_surjective e.toFun p hsurj, ?_,
    coverPullbackProjection_regular e.toFun p hreg, ?_⟩
  · exact connectedSpace_of_homotopyEquiv E
  · exact (acyclic_iff_of_homotopyEquiv E).mpr hac

theorem hasAcyclicRegularCover_homotopyEquiv_iff (K L : TwoComplex)
    (e : ContinuousMap.HomotopyEquiv K L) :
    HasAcyclicRegularCover K ↔ HasAcyclicRegularCover L :=
  ⟨hasAcyclicRegularCover_of_homotopyEquiv L K e.symm,
    hasAcyclicRegularCover_of_homotopyEquiv K L e⟩

end Whitehead
