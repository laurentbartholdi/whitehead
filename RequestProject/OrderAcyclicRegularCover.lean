module

public import RequestProject.OrderUniversalRealizationAcyclicity

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular Topology
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

/-- Actual strict edge-cycle fillings give genuine singular one-cycle fillings. -/
theorem orderRealization_oneCycle_bounds_of_strict_fillings
    (hfill : ∀ c : StrictOrdEdge P →₀ ℤ, bdry1 (strictOrderCx P) c = 0 →
      ∃ b : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) b = c)
    (c : Chain (orderNerveRealization P) 1) (hc : boundary 0 c = 0) :
    ∃ b : Chain (orderNerveRealization P) 2, boundary 1 b = c := by
  obtain ⟨z, hz, hd, hz0, b, hb⟩ := orderNerveRealization_cycle_nerveRepresentative 0 c hc
  obtain ⟨a, ha, ha0⟩ := nerve_oneCycle_filling_of_strict hfill z hz hd hz0
  refine ⟨b + orderNerveGradedRealize P 2 a, ?_⟩
  rw [map_add, hb, orderNerveGradedRealize_boundary 1 ha, ha0]
  abel

theorem orderRealization_homology_one_isZero_of_strict_fillings
    (hfill : ∀ c : StrictOrdEdge P →₀ ℤ, bdry1 (strictOrderCx P) c = 0 →
      ∃ b : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) b = c) :
    Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)) := by
  have he : (complex (orderNerveRealization P)).ExactAt 1 := by
    rw [HomologicalComplex.exactAt_iff' (K := complex (orderNerveRealization P))
      (i := 2) (j := 1) (k := 0) (ChainComplex.prev ℕ 1) (ChainComplex.next_nat_succ 0)]
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro c hc
    change (complex (orderNerveRealization P)).d 1 0 c = 0 at hc
    rw [complex_d] at hc
    change ∃ b : Chain (orderNerveRealization P) 2,
      (complex (orderNerveRealization P)).d 2 1 b = c
    rw [complex_d]
    exact orderRealization_oneCycle_bounds_of_strict_fillings hfill c hc
  exact he.isZero_homology.of_iso (homologyMathlibIso (orderNerveRealization P) 1).symm

/-- Acyclicity of the actual strict cellular complex implies the exact singular
acyclicity of Challenge, for every two-dimensional order realization. -/
theorem orderRealization_acyclic_of_strict_isAcyclic [(nerve P).HasDimensionLE 2]
    (hP : IsAcyclic (strictOrderCx P)) : Whitehead.Acyclic (orderNerveRealization P) := by
  apply (orderRealization_acyclic_iff_homology_one_two P).mpr
  refine ⟨orderRealization_homology_one_isZero_of_strict_fillings hP.h1,
    orderRealization_homology_two_isZero_of_strict_cycles_zero P ?_⟩
  intro c hc
  exact hP.h2 (hc.trans (map_zero _).symm)

namespace IsPosetCover

/-- A connected acyclic strict cellular cover with transitive order deck maps
realizes to a genuine acyclic regular cover. The cover need not be universal. -/
theorem hasAcyclicRegularCover [Nonempty Q] [(nerve Q).HasDimensionLE 2]
    {f : P → Q} (hf : IsPosetCover f)
    (hP : IsConnected (orderCx P)) (hQ : IsConnected (orderCx Q))
    (hdeck : ∀ v w : P, f v = f w →
      ∃ e : P ≃o P, (∀ p, f (e p) = f p) ∧ e v = w)
    (hacyc : IsAcyclic (strictOrderCx P)) :
    Whitehead.HasAcyclicRegularCover (orderNerveTwoComplex Q hQ) := by
  classical
  obtain ⟨q⟩ := (inferInstance : Nonempty Q)
  obtain ⟨p, _⟩ := hf.surj q
  letI : Nonempty P := ⟨p⟩
  letI := hf.realization_hasDimensionLE 2
  letI := orderNerveRealization_pathConnectedSpace P hP
  exact ⟨orderNerveRealization P, inferInstance,
    ⟨orderNerveRealizationMap f hf.mono, (orderNerveRealizationMap f hf.mono).hom.continuous⟩,
    hf.realizationMap_isCoveringMap, hf.realizationMap_surjective,
    inferInstance, hf.realizationMap_regular hdeck,
    orderRealization_acyclic_of_strict_isAcyclic hacyc⟩

end IsPosetCover
end FiniteChains.Comb
