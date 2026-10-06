module

public import RequestProject.PresPosetDimension
public import RequestProject.OrderUniversalPosetCells

@[expose] public section

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

/-- The genuine universal-cover endpoint strictly raises comparable vertices. -/
theorem uOrderEnd_strictMono : StrictMono (uOrderEnd (P := P) (a := a)) := by
  intro v w h
  apply lt_of_le_of_ne (uOrderEnd_monotone h.le)
  intro he
  exact (ne_of_lt h) (uOrder_up_injective (le_refl v) h.le he)

end FiniteChains.Comb

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u}

/-- Dimension two persists in the actual path-class universal cover. -/
theorem presPos_cover_strict_three_flags_empty (w : J → List (α × Bool)) (a : PresPos w) :
    IsEmpty (StrictOrdTet (UOrder (PresPos w) a)) := by
  refine ⟨fun t => ?_⟩
  have h01 := presPosDimension_strictMono w (uOrderEnd_strictMono t.2.1)
  have h12 := presPosDimension_strictMono w (uOrderEnd_strictMono t.2.2.1)
  have h23 := presPosDimension_strictMono w (uOrderEnd_strictMono t.2.2.2)
  have hb := presPosDimension_le_two w (uOrderEnd t.1.2.2.2)
  omega

theorem presPos_cover_normalized_three_boundary_zero (w : J → List (α × Bool))
    (a : PresPos w) (y : OrdTet (UOrder (PresPos w) a) →₀ ℤ) :
    normalizeOrdChain2 (ordBoundary3 y) = 0 := by
  haveI := presPos_cover_strict_three_flags_empty w a
  have hy : normalizeOrdChain3 y = 0 := by
    ext t
    exact isEmptyElim t
  rw [normalizeOrdChain2_ordBoundary3, hy, map_zero]

end FiniteChains.PresModel
