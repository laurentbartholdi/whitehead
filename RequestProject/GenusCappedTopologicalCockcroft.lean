import RequestProject.GenusCappedSingularHomologyPushdown
import RequestProject.OrderRealizationCockcroft
import RequestProject.ChamberZConnected
import RequestProject.PresPosetConnected

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel
variable {V : Type} [DecidableEq V] [Fintype V] {A : CommRel V}
variable (q : ℕ) [NeZero q]

/-- Connectedness of the actual capped quotient is supplied by the construction. -/
theorem cappedSpineQuotient_isConnected
    (w : SpinePresentationRel q ⊕ (Fin q × Bool) → List (SpinePresentationGen q × Bool))
    (hpos : ∀ j, 0 < (w j).length) (att : NeSpx A →o PresPos w) :
    IsConnected (orderCx (Qpos A (PresPos w) att)) := by
  letI : Nonempty (PresPos w) := ⟨ptBase w⟩
  exact qpos_isConnected_of_zpos
    (zpos_isConnected (presPos_isConnected w (fun j => List.length_pos_iff.mp (hpos j))))

/-- The constructed quotient has zero actual Hurewicz map, with no remaining
comparison, generation, or topological covering assumptions. -/
theorem cappedSpineQuotient_isCockcroft
    (w : SpinePresentationRel q ⊕ (Fin q × Bool) → List (SpinePresentationGen q × Bool))
    (hw : ∀ j, FreeGroup.mk (w j) = cappedSpinePresentation q j)
    (hpos : ∀ j, 0 < (w j).length) (att : NeSpx A →o PresPos w) :
    Whitehead.IsCockcroft (orderNerveRealization (Qpos A (PresPos w) att)) := by
  apply (orderRealization_isCockcroft_iff (qNew (A := A) (att := att) (ptBase w))
    (cappedSpineQuotient_isConnected q w hpos att)).mpr
  exact cappedSpineQuotient_homology_pushdown_map_zero q w hw hpos att

end FiniteChains.Davis.Genus
