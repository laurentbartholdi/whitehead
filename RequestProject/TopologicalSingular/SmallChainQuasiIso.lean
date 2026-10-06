module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.SmallChainComplex
public import Mathlib.Algebra.Homology.QuasiIso

@[expose] public section

/-! # The small-chain theorem for an arbitrary open cover

The quotient of singular chains by small chains is acyclic. This follows
from subdivision and its explicit accumulated homotopy, including degree
zero. The short exact sequence then proves that the actual inclusion of
small chains is a quasi-isomorphism in Mathlib's sense.
-/


namespace FiniteChains.SingularSubdivision

open CategoryTheory CategoryTheory.Limits TopologicalSingular Set

universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}
variable (U : ι → Set X)

section Eventual

variable (hsmall : ∀ n (c : Chain X n), ∃ k, ((subdivide n)^[k]) c ∈ smallChains U n)

include hsmall in
theorem smallQuotient_bounds_zero_of_subdivision (q : SmallQuotient U 0) :
    q ∈ LinearMap.range (smallQuotientBoundary U 0) := by
  obtain ⟨c, rfl⟩ := smallProjection_surjective U 0 q
  obtain ⟨k, hk⟩ := hsmall 0 c
  have hp := congrArg (smallProjection U 0) (iteratedHomotopy_identity_zero k c)
  rw [map_sub, (smallProjection_eq_zero_iff U 0 _).mpr hk, zero_sub] at hp
  refine ⟨-smallProjection U 1 (iteratedHomotopy 0 k c), ?_⟩
  rw [map_neg, smallQuotientBoundary_projection, hp, neg_neg]

include hsmall in
theorem smallQuotient_cycle_bounds_of_subdivision (n : ℕ) (q : SmallQuotient U (n + 1))
    (hq : smallQuotientBoundary U n q = 0) :
    q ∈ LinearMap.range (smallQuotientBoundary U (n + 1)) := by
  obtain ⟨c, rfl⟩ := smallProjection_surjective U (n + 1) q
  have hc : boundary n c ∈ smallChains U n := (smallProjection_eq_zero_iff U n _).mp hq
  obtain ⟨k, hk⟩ := hsmall (n + 1) c
  have hH := iteratedHomotopy_mem_small U k n hc
  have hp := congrArg (smallProjection U (n + 1)) (iteratedHomotopy_identity_succ k n c)
  rw [map_add, map_sub, (smallProjection_eq_zero_iff U (n + 1) _).mpr hk,
    (smallProjection_eq_zero_iff U (n + 1) _).mpr hH, add_zero, zero_sub] at hp
  refine ⟨-smallProjection U (n + 2) (iteratedHomotopy (n + 1) k c), ?_⟩
  rw [map_neg, smallQuotientBoundary_projection, hp, neg_neg]

include hsmall in
theorem smallQuotient_exact_zero_of_subdivision : (smallQuotientComplex U).ExactAt 0 := by
  rw [HomologicalComplex.exactAt_iff' (K := smallQuotientComplex U) (i := 1) (j := 0) (k := 0)
    (ChainComplex.prev ℕ 0) ChainComplex.next_nat_zero]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro c _
  change ∃ b : SmallQuotient U 1, ((smallQuotientComplex U).d 1 0) b = c
  rw [smallQuotientComplex_d]
  exact smallQuotient_bounds_zero_of_subdivision U hsmall c

include hsmall in
theorem smallQuotient_exact_succ_of_subdivision (n : ℕ) : (smallQuotientComplex U).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' (K := smallQuotientComplex U) (i := n + 2) (j := n + 1) (k := n)
    (ChainComplex.prev ℕ (n + 1)) (ChainComplex.next_nat_succ n)]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro c hc
  change ((smallQuotientComplex U).d (n + 1) n) c = 0 at hc
  rw [smallQuotientComplex_d] at hc
  change ∃ b : SmallQuotient U (n + 2), ((smallQuotientComplex U).d (n + 2) (n + 1)) b = c
  rw [smallQuotientComplex_d]
  exact smallQuotient_cycle_bounds_of_subdivision U hsmall n c hc

include hsmall in
theorem smallQuotient_acyclic_of_subdivision : (smallQuotientComplex U).Acyclic := by
  intro n
  cases n with
  | zero => exact smallQuotient_exact_zero_of_subdivision U hsmall
  | succ n => exact smallQuotient_exact_succ_of_subdivision U hsmall n

end Eventual

variable (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)

include hU hcover in
theorem smallQuotient_bounds_zero (q : SmallQuotient U 0) :
    q ∈ LinearMap.range (smallQuotientBoundary U 0) :=
  smallQuotient_bounds_zero_of_subdivision U (exists_subdivision_small U hU hcover) q

include hU hcover in
theorem smallQuotient_cycle_bounds (n : ℕ) (q : SmallQuotient U (n + 1))
    (hq : smallQuotientBoundary U n q = 0) :
    q ∈ LinearMap.range (smallQuotientBoundary U (n + 1)) :=
  smallQuotient_cycle_bounds_of_subdivision U (exists_subdivision_small U hU hcover) n q hq

include hU hcover in
theorem smallQuotient_exact_zero : (smallQuotientComplex U).ExactAt 0 :=
  smallQuotient_exact_zero_of_subdivision U (exists_subdivision_small U hU hcover)

include hU hcover in
theorem smallQuotient_exact_succ (n : ℕ) : (smallQuotientComplex U).ExactAt (n + 1) :=
  smallQuotient_exact_succ_of_subdivision U (exists_subdivision_small U hU hcover) n

include hU hcover in
theorem smallQuotient_acyclic : (smallQuotientComplex U).Acyclic :=
  smallQuotient_acyclic_of_subdivision U (exists_subdivision_small U hU hcover)

include hU hcover in
theorem smallQuotient_homology_isZero (n : ℕ) : IsZero ((smallQuotientComplex U).homology n) :=
  (smallQuotient_acyclic U hU hcover n).isZero_homology

include hU hcover in
theorem smallInclusion_homology_isIso (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (smallInclusion U) n) := by
  have hs := smallShortComplex_shortExact U
  have hm : Mono (HomologicalComplex.homologyMap (smallInclusion U) n) :=
    (hs.homology_exact₁ (n + 1) n rfl).mono_g
      ((smallQuotient_homology_isZero U hU hcover (n + 1)).eq_zero_of_src _)
  have he : Epi (HomologicalComplex.homologyMap (smallInclusion U) n) :=
    (hs.homology_exact₂ n).epi_f
      ((smallQuotient_homology_isZero U hU hcover n).eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

include hU hcover in
theorem smallInclusion_quasiIso : QuasiIso (smallInclusion U) := by
  constructor
  intro n
  exact (quasiIsoAt_iff_isIso_homologyMap _ _).mpr (smallInclusion_homology_isIso U hU hcover n)

noncomputable def smallHomologyIso (n : ℕ) :
    (smallComplex U).homology n ≅ (complex X).homology n :=
  @asIso _ _ _ _ _ (smallInclusion_homology_isIso U hU hcover n)

theorem smallHomologyIso_hom (n : ℕ) :
    (smallHomologyIso U hU hcover n).hom = HomologicalComplex.homologyMap (smallInclusion U) n := rfl

end FiniteChains.SingularSubdivision
