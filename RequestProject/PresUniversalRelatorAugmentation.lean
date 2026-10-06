module

public import RequestProject.PresUniversalFoxKernelEquiv
public import RequestProject.Cockcroft

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

/-- Augmenting actual relator ring coordinates forgets precisely the actual lifted apex. -/
theorem presUniversalRelatorRingEquiv_augmentation
    (c : PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w)) →₀ ℤ) (j : J) :
    augQ (relSub ρ) (presUniversalRelatorRingEquiv ρ w hw hpos c j) =
      Finsupp.mapDomain (fun p => p.val.2) c j := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [map_add, Finsupp.add_apply, Finsupp.mapDomain_add, hc, hd]
  | single p n =>
    change augQ (relSub ρ)
      (groupCellChainEquiv (presUniversalRelatorGroupChainEquiv ρ w hw hpos
        (Finsupp.single p n)) j) = _
    rw [presUniversalRelatorGroupChainEquiv, Finsupp.domLCongr_single,
      groupCellChainEquiv_single, Finsupp.mapDomain_single]
    change augQ (relSub ρ) (Finsupp.single p.val.2
      (MonoidAlgebra.single ((presGroupCocycle ρ w hw).readVertex (ptBase w) p.val.1) n) j) =
      Finsupp.single p.val.2 n j
    by_cases h : p.val.2 = j
    · subst j
      simp only [Finsupp.single_eq_same, augQ_single]
    · simp [h]

end FiniteChains.PresModel
