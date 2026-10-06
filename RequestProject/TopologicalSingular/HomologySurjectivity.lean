module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

@[expose] public section

namespace FiniteChains.TopologicalSingular
open CategoryTheory

/-- Representatives up to actual boundaries suffice to prove surjectivity
of Mathlib's canonical homology map. -/
theorem shortComplex_homologyMap_surjective_of_representatives
    {S T : ShortComplex (ModuleCat ℤ)} (φ : S ⟶ T)
    (h : ∀ c : T.X₂, T.g c = 0 →
      ∃ z : S.X₂, S.g z = 0 ∧ ∃ b : T.X₁, T.f b = c - φ.τ₂ z) :
    Function.Surjective (ShortComplex.homologyMap φ) := by
  intro q
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective T.homologyπ).mp inferInstance q
  have hyz : T.g (T.iCycles y) = 0 := by
    exact congrArg (fun f => f y) T.iCycles_g
  obtain ⟨z, hz, b, hb⟩ := h (T.iCycles y) hyz
  let z' : S.cycles := S.moduleCatCyclesIso.inv ⟨z, hz⟩
  have hzi : S.iCycles z' = z := by
    exact congrArg (fun f => f ⟨z, hz⟩) S.moduleCatCyclesIso_inv_iCycles
  refine ⟨S.homologyπ z', ?_⟩
  apply (ModuleCat.mono_iff_injective T.homologyι).mp inferInstance
  rw [← hy]
  have hmap := congrArg (fun f => f z') (ShortComplex.π_homologyMap_ι φ)
  change T.homologyι ((ShortComplex.homologyMap φ) (S.homologyπ z')) =
    T.pOpcycles (φ.τ₂ (S.iCycles z')) at hmap
  have hπ := congrArg (fun f => f y) T.homology_π_ι
  change T.homologyι (T.homologyπ y) = T.pOpcycles (T.iCycles y) at hπ
  rw [hmap, hπ, hzi]
  apply (T.moduleCat_pOpcycles_eq_iff _ _).mpr
  refine ⟨-b, ?_⟩
  rw [map_neg, hb]
  abel

theorem shortComplex_homologyMap_epi_of_representatives
    {S T : ShortComplex (ModuleCat ℤ)} (φ : S ⟶ T)
    (h : ∀ c : T.X₂, T.g c = 0 →
      ∃ z : S.X₂, S.g z = 0 ∧ ∃ b : T.X₁, T.f b = c - φ.τ₂ z) :
    Epi (ShortComplex.homologyMap φ) :=
  (ModuleCat.epi_iff_surjective _).mpr (shortComplex_homologyMap_surjective_of_representatives φ h)

end FiniteChains.TopologicalSingular
