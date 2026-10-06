import RequestProject.HomeomorphContinuousMap
import RequestProject.TopologicalOrderCoverStarLift

/-! The continuous closed-star lift takes every reconstructed vertex to
its actual point in the given covering space. This is the overlap datum
needed to glue the local lifts. Unverified source. -/

noncomputable section
namespace FiniteChains.Comb.TopologicalOrderCover
open CategoryTheory Simplicial Topology
open scoped unitInterval Classical
variable {P : Type} [PartialOrder P] {E : Type} [TopologicalSpace E]
  (p : C(E, orderNerveRealization P)) (hp : IsCoveringMap p)

theorem starBaseMap_mem (q : P) (x : orderNerveRealization (orderNerveVertexStar P q)) :
    starBaseMap q x ∈ (orderNerveRealizationSubcomplex P (orderNerveVertexStar P q) :
      Set (orderNerveRealization P)) := by
  have h := (orderNerveRealizationSubtypeHomeomorph (orderNerveVertexStar P q) x).property
  rw [orderNerveRealizationSubtypeHomeomorph_coe] at h
  exact h

def starLiftFibre (v : Cover p hp) (w : orderNerveVertexStar P v.1) :
    p ⁻¹' {orderNerveRealizationVertex w.val} :=
  ⟨starLift p hp v (orderNerveRealizationVertex w),
    (starLift_projection p hp v _).trans (orderNerveRealizationMap_vertex _ _ w)⟩

theorem starLiftFibre_center (v : Cover p hp) :
    starLiftFibre p hp v (starCenter v.1) = v.2 :=
  Subtype.ext (starLift_center p hp v)

theorem starLiftFibre_transport (v : Cover p hp)
    (w z : orderNerveVertexStar P v.1) (hwz : w ≤ z) :
    hp.monodromy (Path.Homotopic.Quotient.mk (orderNerveRealizationEdgePath (show w.val ≤ z.val from hwz)))
      (starLiftFibre p hp v w) = starLiftFibre p hp v z := by
  let γ := orderNerveRealizationEdgePath hwz
  let β : Path (orderNerveRealizationVertex w.val) (orderNerveRealizationVertex z.val) :=
    { toFun := fun t => starBaseMap v.1 (γ t)
      continuous_toFun := (starBaseMap v.1).continuous.comp γ.continuous
      source' := by rw [γ.source]; exact orderNerveRealizationMap_vertex _ _ w
      target' := by rw [γ.target]; exact orderNerveRealizationMap_vertex _ _ z }
  have hβσ : β.Homotopic (orderNerveRealizationEdgePath (show w.val ≤ z.val from hwz)) := by
    letI := orderNerveRealization_closedStar_contractible v.1
    apply paths_homotopic_of_range_subset
      (A := (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v.1) :
        Set (orderNerveRealization P))) (by
        exact inferInstanceAs (SimplyConnectedSpace
          (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v.1) : Set (orderNerveRealization P))))
    · rintro x ⟨t, rfl⟩
      exact starBaseMap_mem v.1 (γ t)
    · exact orderNerveRealizationEdgePath_supported (P := P) (show w.val ≤ z.val from hwz) v.1 w.property z.property
  rw [← show Path.Homotopic.Quotient.mk β =
    Path.Homotopic.Quotient.mk (orderNerveRealizationEdgePath (show w.val ≤ z.val from hwz))
      from Quotient.sound hβσ]
  let Γ : C(I, E) := (starLift p hp v).comp γ.toContinuousMap
  have h₀ : β 0 = p (starLiftFibre p hp v w).val :=
    β.source.trans (starLiftFibre p hp v w).property.symm
  have hΓ : Γ = hp.liftPath β (starLiftFibre p hp v w).val h₀ := by
    apply (hp.eq_liftPath_iff' h₀).mpr
    constructor
    · funext t
      exact starLift_projection p hp v (γ t)
    · change starLift p hp v (γ 0) = starLift p hp v (orderNerveRealizationVertex w)
      rw [γ.source]
  apply Subtype.ext
  change hp.liftPath β (starLiftFibre p hp v w).val h₀ 1 =
    starLift p hp v (orderNerveRealizationVertex z)
  rw [← hΓ]
  change starLift p hp v (γ 1) = _
  rw [γ.target]

def projectedComparable (v w : Cover p hp) (hw : w ≤ v ∨ v ≤ w) :
    orderNerveVertexStar P v.1 :=
  ⟨w.1, hw.elim (fun h => Or.inl ((projection_monotone p hp) h))
    (fun h => Or.inr ((projection_monotone p hp) h))⟩

theorem starLift_vertex (v w : Cover p hp) (hw : w ≤ v ∨ v ≤ w) :
    starLift p hp v (orderNerveRealizationVertex (projectedComparable p hp v w hw)) =
      point p hp w := by
  let z := projectedComparable p hp v w hw
  have hz : starLiftFibre p hp v z = w.2 := by
    rcases hw with hwv | hvw
    · have hle : z ≤ starCenter v.1 := (projection_monotone p hp) hwv
      apply (hp.monodromy_bijective
        (Path.Homotopic.Quotient.mk (orderNerveRealizationEdgePath hle))).1
      rw [starLiftFibre_transport p hp v z (starCenter v.1) hle,
        starLiftFibre_center]
      exact (comparable_transport p hp hwv).symm
    · have hle : starCenter v.1 ≤ z := (projection_monotone p hp) hvw
      have h := starLiftFibre_transport p hp v (starCenter v.1) z hle
      rw [starLiftFibre_center] at h
      exact h.symm.trans (comparable_transport p hp hvw)
  exact congrArg Subtype.val hz

end FiniteChains.Comb.TopologicalOrderCover
