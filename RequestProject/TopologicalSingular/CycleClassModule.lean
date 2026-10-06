module

public import RequestProject.TopologicalSingular.CycleClasses

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular
open CategoryTheory
universe u

theorem shortComplexCycleClass_smul (S : ShortComplex (ModuleCat.{u} ℤ))
    (r : ℤ) (c : S.X₂) (hc : S.g c = 0) :
    shortComplexCycleClass S (r • c) (by rw [map_zsmul, hc, zsmul_zero]) =
      r • shortComplexCycleClass S c hc := by
  apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
  simp only [map_zsmul, shortComplexCycleClass_i]

theorem shortComplexCycleClass_surjective (S : ShortComplex (ModuleCat.{u} ℤ))
    (q : S.homology) : ∃ (c : S.X₂) (hc : S.g c = 0), shortComplexCycleClass S c hc = q := by
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance q
  have hc : S.g (S.iCycles y) = 0 := congrArg (fun f => f y) S.iCycles_g
  refine ⟨S.iCycles y, hc, ?_⟩
  apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
  rw [shortComplexCycleClass_i, ← hy]
  exact (congrArg (fun f => f y) S.homology_π_ι).symm

variable {X : Type u} [TopologicalSpace X]

theorem singularCycleClass_smul (n : ℕ) (r : ℤ) (c : Chain X (n + 1)) (hc : boundary n c = 0) :
    singularCycleClass n (r • c) (by rw [map_smul, hc, smul_zero]) =
      r • singularCycleClass n c hc := by
  simpa only [singularCycleClass, int_smul_eq_zsmul] using
    (shortComplexCycleClass_smul ((complex X).sc (n + 1)) r c (singularCycle_condition n hc))

/-- Taking a homology class is linear on the actual kernel of the boundary. -/
noncomputable def singularCycleClassLinear (n : ℕ) :
    LinearMap.ker (boundary (X := X) n) →ₗ[ℤ] (complex X).homology (n + 1) where
  toFun c := singularCycleClass n c.val c.property
  map_add' c d := singularCycleClass_add n c.val d.val c.property d.property
  map_smul' r c := by
    exact (singularCycleClass_smul n r c.val c.property).trans
      (int_smul_eq_zsmul (inferInstance : Module ℤ ((complex X).homology (n + 1))) r _).symm

theorem singularCycleClass_representative (n : ℕ) (q : (complex X).homology (n + 1)) :
    ∃ (c : Chain X (n + 1)) (hc : boundary n c = 0), singularCycleClass n c hc = q := by
  obtain ⟨c, hc, hq⟩ := shortComplexCycleClass_surjective ((complex X).sc (n + 1)) q
  have hz : boundary n c = 0 := by
    change (complex X).d (n + 1) ((ComplexShape.down ℕ).next (n + 1)) c = 0 at hc
    rw [ChainComplex.next_nat_succ, complex_d] at hc
    exact hc
  exact ⟨c, hz, hq⟩

end FiniteChains.TopologicalSingular
