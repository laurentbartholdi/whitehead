module

public import RequestProject.PresUniversalRelatorMidpointReading
public import RequestProject.PresCoverCylinderRelatorBoundary

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u v
variable {α J : Type u} {G : Type v} [Group G]
  (w : J → List (α × Bool)) (hpos : ∀ j, 0 < (w j).length)
  (gen : α → G) (hrel : ∀ j, wordVal gen (w j) = 1)

/-- The actual collapse in the universal presentation cover preserves actual vertex reading. -/
theorem presUniversalCylinderCollapse_reading
    (p : {p : UOrder (PresPos w) (ptBase w) //
      uOrderEnd p ∈ coneAdjBaseSet (S := circSet w)}) :
    (presCoc w gen hrel).readVertex (ptBase w)
      (presCoverCylinderCollapse w uOrderEnd (presUniversalEnd_isPosetCover w hpos) p).val =
        (presCoc w gen hrel).readVertex (ptBase w) p.val := by
  let f := uOrderEnd (P := PresPos w) (a := ptBase w)
  let hf := presUniversalEnd_isPosetCover w hpos
  let q := presCoverCylinderCollapse w f hf p
  have hle : p.val ≤ q.val :=
    (coneAdjCoverBaseEnd_isPosetCover f hf).le_upTransform
      (cylCollapse (aHom w)) (le_cylIn_cylRetr (aHom w)) p
  change (presCoc w gen hrel).readVertex (ptBase w) q.val = _
  rw [(presCoc w gen hrel).readVertex_of_le (ptBase w) p.val q.val hle]
  change (presCoc w gen hrel).readVertex (ptBase w) p.val *
    (presCoc w gen hrel).val (f p.val) (f q.val) = _
  rw [← coneAdjCoverBaseEnd_spec f p, ← coneAdjCoverBaseEnd_spec f q]
  change (presCoc w gen hrel).readVertex (ptBase w) p.val *
    roseVal gen (cylRetr (aHom w) (coneAdjCoverBaseEnd f p))
      (cylRetr (aHom w) (coneAdjCoverBaseEnd f q)) = _
  have hq : coneAdjCoverBaseEnd f q = cylCollapse (aHom w) (coneAdjCoverBaseEnd f p) :=
    cylinderCoverCollapse_projection w (coneAdjCoverBaseEnd_isPosetCover f hf) p
  rw [hq]
  change (presCoc w gen hrel).readVertex (ptBase w) p.val *
    roseVal gen (cylRetr (aHom w) (coneAdjCoverBaseEnd f p))
      (cylRetr (aHom w) (coneAdjCoverBaseEnd f p)) = _
  rw [roseVal_self, mul_one]

/-- The actual collapsed lifted-relator midpoint has the same signed prefix reading. -/
theorem presUniversalRelator_collapsed_midpoint_reading
    (p : PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w)))
    (k : Fin (w p.val.2).length) :
    (presCoc w gen hrel).readVertex (ptBase w)
      (presCoverCylinderCollapse (P := UOrder (PresPos w) (ptBase w)) w uOrderEnd
        (presUniversalEnd_isPosetCover w hpos)
        (presCoverCircleCylinderInclusion (P := UOrder (PresPos w) (ptBase w)) w uOrderEnd
          (presUniversalEnd_isPosetCover w hpos) p
          (relatorCirclePoint w p.val.2 k CPos.cmid))).val =
      (presCoc w gen hrel).readVertex (ptBase w) p.val.1 *
        (prefixVal w gen p.val.2 k.val *
          (if ((w p.val.2)[k.val]).2 then 1 else (gen ((w p.val.2)[k.val]).1)⁻¹)) := by
  rw [presUniversalCylinderCollapse_reading w hpos gen hrel]
  exact presUniversalRelator_midpoint_reading w hpos gen hrel p k

end FiniteChains.PresModel
