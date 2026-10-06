module

public import RequestProject.ChamberQuotientPushdownFillings
public import RequestProject.GenusCappedPosetCyclePushdown

@[expose] public section

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel
variable {V : Type} [DecidableEq V] [Fintype V] {A : CommRel V}
variable (q : ℕ) [NeZero q]

/-- Genuine capped-spine zero homology pushdown persists in the actual quotient
chamber extension, with the required base filling proved rather than assumed. -/
theorem cappedSpineQuotient_pushdown_filling
    (w : SpinePresentationRel q ⊕ (Fin q × Bool) → List (SpinePresentationGen q × Bool))
    (hw : ∀ j, FreeGroup.mk (w j) = cappedSpinePresentation q j)
    (hpos : ∀ j, 0 < (w j).length)
    (att : NeSpx A →o PresPos w)
    (z : UF (orderCx (Qpos A (PresPos w) att))
      (qNew (A := A) (att := att) (ptBase w)) →₀ ℤ)
    (hz : Comb.bdry2 (uCover (orderCx (Qpos A (PresPos w) att))
      (qNew (A := A) (att := att) (ptBase w))) z = 0) :
    ∃ y : OrdTet (Qpos A (PresPos w) att) →₀ ℤ,
      chain2 (univProj (X := orderCx (Qpos A (PresPos w) att))
        (x₀ := qNew (A := A) (att := att) (ptBase w))) z = ordBoundary3 y := by
  apply qCover_pushdown_filling_of_base (ptBase w)
    (presPos_isConnected w (fun j => List.length_pos_iff.mp (hpos j))) _ z hz
  intro c hc
  exact ⟨_, cappedSpinePoset_path_cover_pushdown_boundary q w hw hpos c hc⟩

/-- The genuine capped-spine quotient extension has zero universal-cover
pushdown map on second integral order-nerve homology. -/
theorem cappedSpineQuotient_homology_pushdown_map_zero
    (w : SpinePresentationRel q ⊕ (Fin q × Bool) → List (SpinePresentationGen q × Bool))
    (hw : ∀ j, FreeGroup.mk (w j) = cappedSpinePresentation q j)
    (hpos : ∀ j, 0 < (w j).length)
    (att : NeSpx A →o PresPos w) :
    orderNerveH2Map
      (uOrderEnd : UOrder (Qpos A (PresPos w) att)
        (qNew (A := A) (att := att) (ptBase w)) → Qpos A (PresPos w) att)
      uOrderEnd_monotone = 0 :=
  qCover_homology_pushdown_map_zero (ptBase w)
    (presPos_isConnected w (fun j => List.length_pos_iff.mp (hpos j)))
    (cappedSpinePoset_homology_pushdown_map_zero q w hw hpos)

end FiniteChains.Davis.Genus
