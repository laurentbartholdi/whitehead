import RequestProject.TopologicalOrderCoverHomeomorph
import RequestProject.OrderNerveConnectedReflection
import RequestProject.OrderNerveCoverDimension
import RequestProject.OrderNerveTwoComplex
import RequestProject.OrderStrictAcyclicityComparison
import RequestProject.TopologicalSingular.MathlibComparison

/-! Reverse cover dictionary for the original topological definition.
The total space, projection, and deck action are constructed from the
given actual covering; acyclicity follows from its actual homeomorphism.
Unverified source. -/

noncomputable section
namespace FiniteChains.Comb.TopologicalOrderCover
open CategoryTheory Topology
open scoped Classical
variable {P : Type} [PartialOrder P] {E : Type} [TopologicalSpace E]
  (p : C(E, orderNerveRealization P)) (hp : IsCoveringMap p)
  (hs : Function.Surjective p)

include hs in
theorem realization_connected [ConnectedSpace E] :
    ConnectedSpace (orderNerveRealization (Cover p hp)) :=
  (realizationHomeomorph p hp hs).symm.surjective.connectedSpace
    (realizationHomeomorph p hp hs).symm.continuous

include hs in
theorem orderCover_connected [ConnectedSpace E] : IsConnected (orderCx (Cover p hp)) := by
  letI := realization_connected p hp hs
  exact orderCx_isConnected_of_realization

include hs in
theorem strictCover_connected [ConnectedSpace E] : IsConnected (strictOrderCx (Cover p hp)) :=
  strictOrderCx_isConnected (orderCover_connected p hp hs)

include hs in
theorem strictCover_acyclic [ConnectedSpace E] [(nerve P).HasDimensionLE 2]
    (hac : Whitehead.Acyclic E) : IsAcyclic (strictOrderCx (Cover p hp)) := by
  letI := realization_connected p hp hs
  obtain ⟨x⟩ := (inferInstance : Nonempty (orderNerveRealization (Cover p hp)))
  obtain ⟨n, s, z, hz⟩ := orderNerveRealizationSimplex_jointly_surjective (Cover p hp) x
  letI : Nonempty (Cover p hp) := ⟨s.obj 0⟩
  letI := (projection_isPosetCover p hp hs).realization_hasDimensionLE 2
  apply (orderRealization_acyclic_iff_strict_isAcyclic (Cover p hp)
    (orderCover_connected p hp hs)).mp
  exact (Whitehead.acyclic_iff_of_homotopyEquiv
    (realizationHomeomorph p hp hs).toHomotopyEquiv).mpr hac

/-- The returned action has the edge and face compatibility needed by
actual regular-cover chain descent, in addition to ordinary regularity. -/
theorem reconstructed_cover_conclusions [ConnectedSpace E] [(nerve P).HasDimensionLE 2]
    (hr : Whitehead.Regular p) (hac : Whitehead.Acyclic E) :
    IsCovering (strictProjection p hp hs) ∧
    IsRegular (strictProjection p hp hs) (strictDeckAction p hp) ∧
    IsConnected (strictOrderCx (Cover p hp)) ∧
    IsAcyclic (strictOrderCx (Cover p hp)) ∧
    (∀ g e, (strictProjection p hp hs).onE ((strictDeckAction p hp).smulE g e) =
      (strictProjection p hp hs).onE e) ∧
    (∀ g t, (strictProjection p hp hs).onF ((strictDeckAction p hp).smulF g t) =
      (strictProjection p hp hs).onF t) :=
  ⟨strictProjection_isCovering p hp hs, strictProjection_isRegular p hp hs hr,
    strictCover_connected p hp hs, strictCover_acyclic p hp hs hac,
    strictDeck_edges p hp hs, strictDeck_faces p hp hs⟩

end TopologicalOrderCover

open CategoryTheory Topology

theorem strict_hasAcyclicRegularCover_of_topological
    (P : Type) [PartialOrder P] [Nonempty P] [(nerve P).HasDimensionLE 2]
    (hP : IsConnected (orderCx P))
    (h : Whitehead.HasAcyclicRegularCover (orderNerveTwoComplex P hP)) :
    HasAcyclicRegularCover (strictOrderCx P) := by
  obtain ⟨E, tE, p, hp, hs, hconn, hr, hac⟩ := h
  letI := tE
  letI := hconn
  exact ⟨strictOrderCx (TopologicalOrderCover.Cover p hp),
    TopologicalOrderCover.deckSubgroup p, inferInstance,
    TopologicalOrderCover.strictProjection p hp hs,
    TopologicalOrderCover.strictDeckAction p hp,
    TopologicalOrderCover.strictProjection_isCovering p hp hs,
    TopologicalOrderCover.strictProjection_isRegular p hp hs hr,
    TopologicalOrderCover.strictCover_connected p hp hs,
    TopologicalOrderCover.strictCover_acyclic p hp hs hac⟩

end FiniteChains.Comb
