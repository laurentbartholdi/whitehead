module

public import RequestProject.QCubeCubicalTwoBoundary

@[expose] public section

/-! Actual edges of a square in any decreasing coordinate frame. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qSquareSmallFacet_ordered (c : QSquare A) {a b : V}
    (h : b < a) (hs : c.1.spx = {a, b}) (s : ZMod 2) :
    (qSquareSmallFacet c s).1 = qCubeFacet c.1 b s := by
  obtain ⟨_, hr⟩ := qSquare_frame_unique c h hs
  change qCubeFacet c.1 (qSquareRight c) s = _
  rw [hr]

theorem qSquareLargeFacet_ordered (c : QSquare A) {a b : V}
    (h : b < a) (hs : c.1.spx = {a, b}) (s : ZMod 2) :
    (qSquareLargeFacet c s).1 = qCubeFacet c.1 a s := by
  obtain ⟨hl, _⟩ := qSquare_frame_unique c h hs
  change qCubeFacet c.1 (qSquareLeft c) s = _
  rw [hl]

end FiniteChains.Davis
