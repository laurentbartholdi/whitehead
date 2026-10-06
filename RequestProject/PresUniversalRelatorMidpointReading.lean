module

public import RequestProject.PresUniversalReadingPrefix
public import RequestProject.PresUniversalRelatorDeck
public import RequestProject.PresCoverRelatorFan

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u v
variable {α J : Type u} {G : Type v} [Group G]
  (w : J → List (α × Bool)) (hpos : ∀ j, 0 < (w j).length)
  (gen : α → G) (hrel : ∀ j, wordVal gen (w j) = 1)

/-- Reading the actual midpoint of an actual lifted relator gives its actual signed prefix. -/
theorem presUniversalRelator_midpoint_reading
    (p : PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w)))
    (k : Fin (w p.val.2).length) :
    (presCoc w gen hrel).readVertex (ptBase w)
      (presCoverCircleInclusion (P := UOrder (PresPos w) (ptBase w)) w uOrderEnd (presUniversalEnd_isPosetCover w hpos) p
        (relatorCirclePoint w p.val.2 k CPos.cmid)) =
      (presCoc w gen hrel).readVertex (ptBase w) p.val.1 *
        (prefixVal w gen p.val.2 k.val *
          (if ((w p.val.2)[k.val]).2 then 1 else (gen ((w p.val.2)[k.val]).1)⁻¹)) := by
  apply presUniversal_midpoint_reading w gen hrel (ptBase w) p.val.2 k.val _
    (List.getElem?_eq_getElem k.isLt)
  · exact (presCoverCircleInclusion_lt_apex (P := UOrder (PresPos w) (ptBase w)) w uOrderEnd
      (presUniversalEnd_isPosetCover w hpos) p _).le
  · exact presCoverConeCircleOrderIso_symm_projection (P := UOrder (PresPos w) (ptBase w)) w uOrderEnd
      (presUniversalEnd_isPosetCover w hpos) p.val.1 p.val.2 p.property _
  · exact p.property

end FiniteChains.PresModel
