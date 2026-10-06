module

public import RequestProject.PresCocyclePerfectCover
public import RequestProject.OrderAcyclicRegularCover
public import RequestProject.PresPosetDimension
public import RequestProject.PresentationChainFinsupp

@[expose] public section

/-! Realization of the explicit perfect-subgroup cocycle cover. All covering,
regularity and singular-acyclicity data are constructed, not additional inputs.
 -/
noncomputable section
namespace FiniteChains.PresModel
open Comb PresCocycleCover CategoryTheory
variable {α J : Type} [DecidableEq α] (w : J → List (α × Bool))
  (hpos : ∀ j, 0 < (w j).length)

def coveredPresentationTwoComplex : Whitehead.TwoComplex := by
  letI : Nonempty (PresPos w) := ⟨ptBase w⟩
  letI : (nerve (PresPos w)).HasDimensionLE 2 :=
    orderNerve_hasDimensionLE (presPosDimension w) (presPosDimension_strictMono w) 2
      (presPosDimension_le_two w)
  exact orderNerveTwoComplex (PresPos w)
    (presPos_isConnected w (fun j => List.length_pos_iff.mp (hpos j)))

theorem coveredPresentation_hasAcyclicRegularCover_of_perfect
    (ρ : J → FreeGroup α) (hw : ∀ j, FreeGroup.mk (w j) = ρ j)
    (H : Subgroup (PresGroup ρ)) [H.Normal]
    (hsat : ∀ v : J →₀ MonoidAlgebra ℤ (PresGroup ρ), FoxSat (foxMatrixPres ρ) v H)
    (hperf : ⁅H, H⁆ = H) :
    Whitehead.HasAcyclicRegularCover (coveredPresentationTwoComplex w hpos) := by
  letI : Nonempty (PresPos w) := ⟨ptBase w⟩
  letI : (nerve (PresPos w)).HasDimensionLE 2 :=
    orderNerve_hasDimensionLE (presPosDimension w) (presPosDimension_strictMono w) 2
      (presPosDimension_le_two w)
  let N := subgroupPreimage ρ H
  let hr := subgroupPreimage_contains_relators w ρ hw H
  exact (quotientCovering w N hr).hasAcyclicRegularCover
    (quotient_isConnected w N hr hpos)
    (presPos_isConnected w (fun j => List.length_pos_iff.mp (hpos j)))
    ((subgroupCoc w ρ hw H).cover_deck_transitive)
    (subgroupCover_isAcyclic w ρ hw hpos H hsat hperf)

/-- The compactness necessity argument produces an actual connected regular
topological cover with vanishing genuine singular homology. -/
theorem coveredPresentation_hasAcyclicRegularCover_of_cellChains
    (ρ : J → FreeGroup α) (hw : ∀ j, FreeGroup.mk (w j) = ρ j)
    (hchains : HasCellChainsLift (foxMatrixPres ρ)) :
    Whitehead.HasAcyclicRegularCover (coveredPresentationTwoComplex w hpos) := by
  obtain ⟨H, hn, _, hs, hp⟩ := fs_exists_perfect_normal_of_cellChains ρ hchains
  letI := hn
  exact coveredPresentation_hasAcyclicRegularCover_of_perfect w hpos ρ hw H hs hp

theorem coveredPresentation_hasAcyclicRegularCover_of_presChains
    (ρ : J → FreeGroup α) (hw : ∀ j, FreeGroup.mk (w j) = ρ j)
    (hchains : ∀ n, Nonempty (PresChainFS ρ n)) :
    Whitehead.HasAcyclicRegularCover (coveredPresentationTwoComplex w hpos) :=
  coveredPresentation_hasAcyclicRegularCover_of_cellChains w hpos ρ hw
    (hasCellChainsLift_of_presChainsFS ρ hchains)

end FiniteChains.PresModel
