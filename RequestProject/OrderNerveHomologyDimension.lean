module

public import RequestProject.OrderNervePositiveHomologyIso
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.AlgebraicTopology.DoldKan.Degeneracies

@[expose] public section

/-! Actual singular homology vanishes above the dimension of the order nerve. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  AlgebraicTopology Simplicial

/-- The normalization projector annihilates every degree in which all simplices
are degenerate. This is a statement about the actual free simplicial module. -/
theorem freeSSet_PInfty_eq_zero (X : SSet) (d n : ℕ)
    [X.HasDimensionLT d] (hn : d ≤ n) :
    (DoldKan.PInfty (X := X ⋙ ModuleCat.free ℤ)).f n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change ((DoldKan.PInfty (X := X ⋙ ModuleCat.free ℤ)).f n).hom c = 0
  induction c using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add c e hc he => rw (config := { transparency := .default }) [map_add, hc, he, add_zero]
  | single s r =>
    have hs : s ∈ X.degenerate n := by
      rw (config := { transparency := .default }) [X.degenerate_eq_top_of_hasDimensionLT d n hn]
      trivial
    obtain ⟨m, hm, θ, y, rfl⟩ := hs
    have hθ : ¬ Mono θ := by
      intro hθ
      exact (not_le_of_gt hm) (SimplexCategory.len_le_of_mono θ)
    have h := DoldKan.degeneracy_comp_PInfty (X ⋙ ModuleCat.free ℤ) n θ hθ
    have hv := congrArg (fun f => f.hom (Finsupp.single y r)) h
    simpa [ModuleCat.free] using hv

/-- Homology of the alternating-face complex vanishes above simplicial dimension. -/
theorem freeSSet_homology_isZero_of_dimension (X : SSet) (d n : ℕ)
    [X.HasDimensionLT d] (hn : d ≤ n) :
    Limits.IsZero ((AlternatingFaceMapComplex.obj (X ⋙ ModuleCat.free ℤ)).homology n) := by
  let K := AlternatingFaceMapComplex.obj (X ⋙ ModuleCat.free ℤ)
  let p : K ⟶ K := DoldKan.PInfty
  have hp : p.f n = 0 := freeSSet_PInfty_eq_zero X d n hn
  have hz : HomologicalComplex.homologyMap p n = 0 := by
    rw (config := { transparency := .default }) [← cancel_epi (K.homologyπ n), HomologicalComplex.homologyπ_naturality,
      comp_zero]
    have hc : HomologicalComplex.cyclesMap p n = 0 := by
      rw (config := { transparency := .default }) [← cancel_mono (K.iCycles n), HomologicalComplex.cyclesMap_i, hp,
        zero_comp, comp_zero]
    rw (config := { transparency := .default }) [hc, zero_comp]
  apply (IsZero.iff_id_eq_zero _).mpr
  have hh := (DoldKan.homotopyPInftyToId (X ⋙ ModuleCat.free ℤ)).homologyMap_eq n
  rw (config := { transparency := .default }) [HomologicalComplex.homologyMap_id] at hh
  exact hh.symm.trans hz

/-- The dimension bound controls the precise singular homology used in Challenge. -/
theorem orderNerve_singularHomology_isZero_of_dimension (P : Type) [PartialOrder P]
    (d n : ℕ) [(nerve P).HasDimensionLE d] (hn : d < n) :
    Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Nat.zero_le d |>.trans_lt hn))
  exact (freeSSet_homology_isZero_of_dimension (nerve P) (d + 1) (k + 1) hn).of_iso
    (orderNervePositiveSingularHomologyIso P k).symm

end FiniteChains.Comb
