import RequestProject.ChamberQuotientStarRetraction
import RequestProject.PosetCoverComparableLifts

/-! Lift the actual downward star retraction in the chosen universal-cover sheet. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

abbrev QLiftedBaseStar (a : Qpos A X att) :=
  {p : UOrder (Qpos A X att) a // InQBaseStar (uOrderEnd p)}

def qBaseIntoStar (a : Qpos A X att) (p : QLiftedBase a) : QLiftedBaseStar a :=
  ⟨p.1, inQBase_in_star p.2⟩

theorem qBaseIntoStar_monotone (a : Qpos A X att) : Monotone (qBaseIntoStar a) :=
  fun _ _ h => h

variable (a : Qpos A X att) (hc : IsConnected (orderCx (Qpos A X att)))

noncomputable def qLiftedStarRetraction (p : QLiftedBaseStar a) : QLiftedBase a :=
  ⟨(uOrderEnd_isPosetCover hc).lowerMapLift Subtype.val
    (fun p : QLiftedBaseStar a => qBaseStarRetraction ⟨uOrderEnd p.1, p.2⟩)
    (fun p => qBaseStarRetraction_le ⟨uOrderEnd p.1, p.2⟩) p, by
      have h := (uOrderEnd_isPosetCover hc).lowerMapLift_spec Subtype.val
        (fun p : QLiftedBaseStar a => qBaseStarRetraction ⟨uOrderEnd p.1, p.2⟩)
        (fun p => qBaseStarRetraction_le ⟨uOrderEnd p.1, p.2⟩) p
      rw [h.2]
      exact qBaseStarRetraction_mem_base _⟩

theorem qLiftedStarRetraction_monotone : Monotone (qLiftedStarRetraction a hc) := by
  intro p r h
  exact (uOrderEnd_isPosetCover hc).lowerMapLift_monotone Subtype.val
    (fun p : QLiftedBaseStar a => qBaseStarRetraction ⟨uOrderEnd p.1, p.2⟩)
    monotone_subtypeVal (fun _ _ h => qBaseStarRetraction_monotone (uOrderEnd_monotone h))
    (fun p => qBaseStarRetraction_le ⟨uOrderEnd p.1, p.2⟩) h

theorem qLiftedStarRetraction_le (p : QLiftedBaseStar a) :
    qBaseIntoStar a (qLiftedStarRetraction a hc p) ≤ p :=
  ((uOrderEnd_isPosetCover hc).lowerMapLift_spec Subtype.val
    (fun p : QLiftedBaseStar a => qBaseStarRetraction ⟨uOrderEnd p.1, p.2⟩)
    (fun p => qBaseStarRetraction_le ⟨uOrderEnd p.1, p.2⟩) p).1

end FiniteChains.Davis
