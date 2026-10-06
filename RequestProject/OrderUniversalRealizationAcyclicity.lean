module

public import RequestProject.OrderTwoDimensionalAcyclicity
public import RequestProject.OrderUniversalRealizationPi2
public import RequestProject.OrderUniversalRealizationSimplyConnected
public import RequestProject.TopologicalSingular.HurewiczIsomorphismConsequences
public import RequestProject.OrderNerveTwoComplex

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory CategoryTheory.Category AlgebraicTopology TopologicalSingular Topology
variable {P : Type} [PartialOrder P] (a : P)
  [(nerve P).HasDimensionLE 2] (hc : IsConnected (orderCx P))

include a hc

/-- Vanishing of the actual strict universal two-cycles makes the constructed
universal topological covering acyclic in every positive singular degree. -/
theorem uOrderRealization_acyclic_of_strict_cycles_zero
    (hz : ∀ c : StrictOrdTri (UOrder P a) →₀ ℤ,
      bdry2 (strictOrderCx (UOrder P a)) c = 0 → c = 0) :
    Whitehead.Acyclic (orderNerveRealization (UOrder P a)) := by
  letI := (uOrderEnd_isPosetCover (a := a) hc).realization_hasDimensionLE 2
  letI := uOrderRealization_simplyConnected a
  exact orderRealization_acyclic_of_simplyConnected_of_strict_cycles_zero _ hz

/-- The actual identity has zero pi2 exactly when the constructed universal
cover is acyclic. This does not assert that every acyclic regular cover is universal. -/
theorem uOrderRealization_acyclic_iff_killsPi2_id :
    Whitehead.Acyclic (orderNerveRealization (UOrder P a)) ↔
      Whitehead.KillsPi2 (ContinuousMap.id (orderNerveRealization P)) := by
  letI := (uOrderEnd_isPosetCover (a := a) hc).realization_hasDimensionLE 2
  letI := uOrderRealization_simplyConnected a
  let p := uOrderRealizationProjection a
  let x := orderNerveRealizationVertex (P := UOrder P a) (UV.base (orderCx P) a)
  have hk : Whitehead.KillsPi2 (ContinuousMap.id (orderNerveRealization P)) ↔
      Whitehead.KillsPi2 (ContinuousMap.id (orderNerveRealization (UOrder P a))) := by
    rw [← Whitehead.killsPi2_covering_precomp_iff p
      (uOrderRealizationProjection_isCoveringMap a hc)
      (uOrderRealizationProjection_surjective a hc)]
    simpa only [ContinuousMap.id_comp, ContinuousMap.comp_id] using
      (Whitehead.killsPi2_covering_postcomp_iff
        (ContinuousMap.id (orderNerveRealization (UOrder P a))) p
        (uOrderRealizationProjection_isCoveringMap a hc))
  rw [hk, killsPi2_iff_singularH2_map_eq_zero x]
  have hid : TopCat.ofHom (ContinuousMap.id (orderNerveRealization (UOrder P a))) =
      𝟙 (orderNerveRealization (UOrder P a)) := rfl
  rw [hid, CategoryTheory.Functor.map_id, ← Limits.IsZero.iff_id_eq_zero]
  rw [orderRealization_acyclic_iff_homology_one_two]
  exact and_iff_right
    (mathlibHomologyOne_isZero_of_simplyConnected (orderNerveRealization (UOrder P a)))

/-- An actual acyclic universal realization supplies all fields of the
acyclic regular covering demanded by the original Challenge statement. -/
theorem orderNerve_hasAcyclicRegularCover_of_universal_acyclic [Nonempty P]
    (hacyc : Whitehead.Acyclic (orderNerveRealization (UOrder P a))) :
    Whitehead.HasAcyclicRegularCover (orderNerveTwoComplex P hc) := by
  letI := uOrderRealization_pathConnectedSpace a
  exact ⟨orderNerveRealization (UOrder P a), inferInstance,
    uOrderRealizationProjection a, uOrderRealizationProjection_isCoveringMap a hc,
    uOrderRealizationProjection_surjective a hc, inferInstance,
    uOrderRealizationProjection_regular a hc, hacyc⟩

theorem orderNerve_hasAcyclicRegularCover_of_strict_cycles_zero [Nonempty P]
    (hz : ∀ c : StrictOrdTri (UOrder P a) →₀ ℤ,
      bdry2 (strictOrderCx (UOrder P a)) c = 0 → c = 0) :
    Whitehead.HasAcyclicRegularCover (orderNerveTwoComplex P hc) :=
  orderNerve_hasAcyclicRegularCover_of_universal_acyclic a hc
    (uOrderRealization_acyclic_of_strict_cycles_zero a hc hz)

theorem orderNerve_hasAcyclicRegularCover_of_killsPi2_id [Nonempty P]
    (hk : Whitehead.KillsPi2 (ContinuousMap.id (orderNerveRealization P))) :
    Whitehead.HasAcyclicRegularCover (orderNerveTwoComplex P hc) :=
  orderNerve_hasAcyclicRegularCover_of_universal_acyclic a hc
    ((uOrderRealization_acyclic_iff_killsPi2_id a hc).mpr hk)

end FiniteChains.Comb
