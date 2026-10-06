import RequestProject.OrderNerveSmallHomotopyAll

namespace FiniteChains.Comb
open CategoryTheory TopologicalSingular SingularSubdivision
variable {P : Type} [PartialOrder P]

/-- Every positive-degree singular cycle has a homogeneous order-chain representative. -/
theorem orderNerveRealization_cycle_nerveRepresentative (n : ℕ)
    (c : Chain (orderNerveRealization P) (n + 1)) (hc : boundary n c = 0) :
    ∃ z : Nerve.Ch P, z ∈ Nerve.Inc P ∧ Nerve.lengthProjection (n + 2) z = z ∧
      Nerve.bdry z = 0 ∧ ∃ b : Chain (orderNerveRealization P) (n + 2),
        boundary (n + 1) b = c - orderNerveGradedRealize P (n + 1) z := by
  obtain ⟨d, hd, hz, a, ha⟩ := orderNerveRealization_exists_small_cycle P n c hc
  let d' : smallChains (orderNerveRealizationOpenStar P) (n + 1) := ⟨d, hd⟩
  have hd' : smallBoundary (orderNerveRealizationOpenStar P) n d' = 0 := Subtype.ext hz
  obtain ⟨b, hb⟩ := orderSmallSingularApproximation_homologous n d' hd'
  refine ⟨orderSmallToNerve P (n + 1) d', orderSmallToNerve_mem_inc _ _,
    orderSmallToNerve_length _ _, ?_, b - a, ?_⟩
  · rw [orderSmallToNerve_boundary, hd', map_zero]
  · rw [map_sub, hb, ha]
    change d - orderNerveGradedRealize P (n + 1) (orderSmallToNerve P (n + 1) d') - (d - c) = _
    abel

/-- Augmented order-chain exactness gives actual positive-degree singular fillings. -/
theorem orderNerveRealization_cycle_bounds_of_nerve
    (hP : ∀ z : Nerve.Ch P, z ∈ Nerve.Inc P → Nerve.bdry z = 0 →
      ∃ b ∈ Nerve.Inc P, Nerve.bdry b = z)
    (n : ℕ) (c : Chain (orderNerveRealization P) (n + 1)) (hc : boundary n c = 0) :
    ∃ b : Chain (orderNerveRealization P) (n + 2), boundary (n + 1) b = c := by
  obtain ⟨z, hz, _, hz0, b, hb⟩ := orderNerveRealization_cycle_nerveRepresentative n c hc
  obtain ⟨a, ha, ha0⟩ := hP z hz hz0
  refine ⟨b + orderNerveGradedRealize P (n + 2) a, ?_⟩
  rw [map_add, hb, orderNerveGradedRealize_boundary (n + 1) ha, ha0]
  abel

/-- The comparison proves vanishing for the precise singular homology in Theorem A. -/
theorem orderNerveRealization_acyclic_of_nerve
    (hP : ∀ z : Nerve.Ch P, z ∈ Nerve.Inc P → Nerve.bdry z = 0 →
      ∃ b ∈ Nerve.Inc P, Nerve.bdry b = z) :
    Whitehead.Acyclic (orderNerveRealization P) := by
  intro k hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
  have he : (complex (orderNerveRealization P)).ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff' (K := complex (orderNerveRealization P))
      (i := n + 2) (j := n + 1) (k := n)
      (ChainComplex.prev ℕ (n + 1)) (ChainComplex.next_nat_succ n)]
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro c hc
    change (complex (orderNerveRealization P)).d (n + 1) n c = 0 at hc
    rw [complex_d] at hc
    change ∃ b : Chain (orderNerveRealization P) (n + 2),
      (complex (orderNerveRealization P)).d (n + 2) (n + 1) b = c
    rw [complex_d]
    exact orderNerveRealization_cycle_bounds_of_nerve hP n c hc
  exact he.isZero_homology.of_iso (homologyMathlibIso (orderNerveRealization P) (n + 1)).symm

end FiniteChains.Comb
