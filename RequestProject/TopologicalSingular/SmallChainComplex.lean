module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.SmallChainHomology
public import RequestProject.TopologicalSingular.SingularHomologySequence

@[expose] public section

/-! # The small singular subcomplex and its quotient

All complexes are defined from the actual singular differential. The
short exact sequence is valid for an arbitrary family of subsets; no
openness or covering assumption is used in this file.
-/


set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.SingularSubdivision

open CategoryTheory CategoryTheory.Limits TopologicalSingular Set

universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}

noncomputable def smallBoundary (U : ι → Set X) (n : ℕ) :
    smallChains U (n + 1) →ₗ[ℤ] smallChains U n :=
  ((boundary n).comp (smallChains U (n + 1)).subtype).codRestrict _
    (fun c => boundary_mem_small U n c.property)

theorem smallBoundary_val (U : ι → Set X) (n : ℕ) (c : smallChains U (n + 1)) :
    (smallBoundary U n c).val = boundary n c.val := rfl

theorem smallBoundary_squared (U : ι → Set X) (n : ℕ) :
    (smallBoundary U n).comp (smallBoundary U (n + 1)) = 0 := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  exact boundary_boundary n c.val

noncomputable def smallComplex (U : ι → Set X) : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of ℤ (smallChains U n))
    (fun n => ModuleCat.ofHom (smallBoundary U n))
    (fun n => ModuleCat.hom_ext (smallBoundary_squared U n))

theorem smallComplex_d (U : ι → Set X) (n : ℕ) :
    (smallComplex U).d (n + 1) n = ModuleCat.ofHom (smallBoundary U n) :=
  by
    unfold smallComplex
    exact ChainComplex.of_d (fun i => ModuleCat.of ℤ (smallChains U i)) (fun i => ModuleCat.ofHom (smallBoundary U i)) n

noncomputable def smallInclusion (U : ι → Set X) : smallComplex U ⟶ complex X :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (smallChains U n).subtype) (fun n => by
      rw [smallComplex_d, complex_d]
      apply ModuleCat.hom_ext
      rfl)

theorem smallInclusion_f (U : ι → Set X) (n : ℕ) :
    (smallInclusion U).f n = ModuleCat.ofHom (smallChains U n).subtype := rfl

abbrev SmallQuotient (U : ι → Set X) (n : ℕ) := Chain X n ⧸ smallChains U n

noncomputable def smallProjection (U : ι → Set X) (n : ℕ) :
    Chain X n →ₗ[ℤ] SmallQuotient U n := (smallChains U n).mkQ

theorem smallProjection_surjective (U : ι → Set X) (n : ℕ) :
    Function.Surjective (smallProjection U n) := (smallChains U n).mkQ_surjective

theorem smallProjection_eq_zero_iff (U : ι → Set X) (n : ℕ) (c : Chain X n) :
    smallProjection U n c = 0 ↔ c ∈ smallChains U n := by
  change c ∈ LinearMap.ker (smallProjection U n) ↔ _
  rw [show LinearMap.ker (smallProjection U n) = smallChains U n from
    (smallChains U n).ker_mkQ]

noncomputable def smallQuotientBoundary (U : ι → Set X) (n : ℕ) :
    SmallQuotient U (n + 1) →ₗ[ℤ] SmallQuotient U n :=
  (smallChains U (n + 1)).mapQ (smallChains U n) (boundary n)
    (fun _ h => boundary_mem_small U n h)

theorem smallQuotientBoundary_projection (U : ι → Set X) (n : ℕ) (c : Chain X (n + 1)) :
    smallQuotientBoundary U n (smallProjection U (n + 1) c) =
      smallProjection U n (boundary n c) := rfl

theorem smallQuotientBoundary_squared (U : ι → Set X) (n : ℕ) :
    (smallQuotientBoundary U n).comp (smallQuotientBoundary U (n + 1)) = 0 := by
  apply LinearMap.ext
  intro q
  obtain ⟨c, rfl⟩ := smallProjection_surjective U (n + 2) q
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, smallQuotientBoundary_projection,
    boundary_boundary, map_zero]

noncomputable def smallQuotientComplex (U : ι → Set X) : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of ℤ (SmallQuotient U n))
    (fun n => ModuleCat.ofHom (smallQuotientBoundary U n))
    (fun n => ModuleCat.hom_ext (smallQuotientBoundary_squared U n))

theorem smallQuotientComplex_d (U : ι → Set X) (n : ℕ) :
    (smallQuotientComplex U).d (n + 1) n = ModuleCat.ofHom (smallQuotientBoundary U n) :=
  by
    unfold smallQuotientComplex
    exact ChainComplex.of_d (fun i => ModuleCat.of ℤ (SmallQuotient U i)) (fun i => ModuleCat.ofHom (smallQuotientBoundary U i)) n

noncomputable def smallProjectionChainMap (U : ι → Set X) : complex X ⟶ smallQuotientComplex U :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (smallProjection U n)) (fun n => by
    rw [complex_d, smallQuotientComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact smallQuotientBoundary_projection U n)

theorem smallProjectionChainMap_f (U : ι → Set X) (n : ℕ) :
    (smallProjectionChainMap U).f n = ModuleCat.ofHom (smallProjection U n) := rfl

theorem smallInclusion_projection_zero (U : ι → Set X) :
    smallInclusion U ≫ smallProjectionChainMap U = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change smallProjection U n c.val = 0
  exact (smallProjection_eq_zero_iff U n _).mpr c.property

noncomputable def smallShortComplex (U : ι → Set X) :
    ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (smallInclusion U) (smallProjectionChainMap U) (smallInclusion_projection_zero U)

theorem smallShortComplex_shortExact (U : ι → Set X) : (smallShortComplex U).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
    change LinearMap.range (smallChains U n).subtype = LinearMap.ker (smallProjection U n)
    rw [Submodule.range_subtype, show LinearMap.ker (smallProjection U n) = smallChains U n from
      (smallChains U n).ker_mkQ]
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact Subtype.val_injective
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact smallProjection_surjective U n

end FiniteChains.SingularSubdivision
