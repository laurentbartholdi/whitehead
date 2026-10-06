import RequestProject.TopologicalSingular.SmallChainQuasiIso
import RequestProject.TopologicalSingular.MathlibComparison

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.SingularSubdivision
open CategoryTheory AlgebraicTopology TopologicalSingular

variable {X : Type} [TopologicalSpace X] {ι : Type}

/-- The actual inclusion of small chains into Mathlib's integral singular complex. -/
noncomputable def smallMathlibInclusion (U : ι → Set X) :
    smallComplex U ⟶ ((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of X) :=
  smallInclusion U ≫ (complexMathlibIso (TopCat.of X)).hom

/-- Subdivision proves the small-chain theorem for Mathlib's singular complex,
in every degree, for any open cover. -/
theorem smallMathlibInclusion_quasiIso (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) :
    QuasiIso (smallMathlibInclusion U) := by
  letI := smallInclusion_quasiIso U hU hcover
  unfold smallMathlibInclusion
  infer_instance

/-- Small chains compute the precise singular homology used in Theorem A. -/
noncomputable def smallMathlibHomologyIso (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) :
    (smallComplex U).homology n ≅ ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of X) :=
  smallHomologyIso U hU hcover n ≪≫ homologyMathlibIso (TopCat.of X) n

theorem smallMathlibHomologyIso_hom (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) :
    (smallMathlibHomologyIso U hU hcover n).hom =
      HomologicalComplex.homologyMap (smallMathlibInclusion U) n := by
  rw [smallMathlibInclusion, HomologicalComplex.homologyMap_comp]
  rfl

end FiniteChains.SingularSubdivision
