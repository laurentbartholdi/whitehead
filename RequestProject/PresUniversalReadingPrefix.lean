import RequestProject.PresPosetPartialOrder
import RequestProject.OrderUniversalCocycleComparability
import RequestProject.PresReadingLetterPrefix

namespace FiniteChains.PresModel
open Comb
universe u v
variable {α J : Type u} {G : Type v} [Group G]
  (w : J → List (α × Bool)) (gen : α → G)
  (hrel : ∀ j, wordVal gen (w j) = 1) (a : PresPos w)

/-- The actual lifted cone midpoint reads as its apex reading times the signed word prefix. -/
theorem presUniversal_midpoint_reading (j : J) (k : ℕ) (b : α × Bool)
    (hb : (w j)[k]? = some b) (p q : UOrder (PresPos w) a) (hle : p ≤ q)
    (hp : uOrderEnd p = iCirc w (TCirc.pt w j k CPos.cmid))
    (hq : uOrderEnd q = apexOf w j) :
    (presCoc w gen hrel).readVertex a p =
      (presCoc w gen hrel).readVertex a q *
        (prefixVal w gen j k * (if b.2 then 1 else (gen b.1)⁻¹)) := by
  rw [(presCoc w gen hrel).readVertex_lower_of_le a p q hle, hp, hq]
  change (presCoc w gen hrel).readVertex a q * (trivVal w gen j k CPos.cmid)⁻¹ = _
  rw [trivVal_cmid_inv_of_get w gen j k b hb]

/-- Actual lifted circle corners read as the apex reading times their actual preceding prefix. -/
theorem presUniversal_corner_reading (j : J) (k : ℕ)
    (p q : UOrder (PresPos w) a) (hle : p ≤ q)
    (hp : uOrderEnd p = iCirc w (TCirc.pt w j k CPos.cor))
    (hq : uOrderEnd q = apexOf w j) :
    (presCoc w gen hrel).readVertex a p =
      (presCoc w gen hrel).readVertex a q * prefixVal w gen j k := by
  rw [(presCoc w gen hrel).readVertex_lower_of_le a p q hle, hp, hq]
  change (presCoc w gen hrel).readVertex a q * ((prefixVal w gen j k)⁻¹)⁻¹ = _
  rw [inv_inv]

/-- Reading is unchanged along the actual cylinder comparability to the attached rose vertex. -/
theorem presUniversal_cylinder_reading (x : TCirc w)
    (p q : UOrder (PresPos w) a) (hle : p ≤ q)
    (hp : uOrderEnd p = iCirc w x)
    (hq : uOrderEnd q = iRose w (aFun w x)) :
    (presCoc w gen hrel).readVertex a q = (presCoc w gen hrel).readVertex a p := by
  rw [(presCoc w gen hrel).readVertex_of_le a p q hle, hp, hq]
  change (presCoc w gen hrel).readVertex a p * roseVal gen (aFun w x) (aFun w x) = _
  rw [roseVal_self, mul_one]

end FiniteChains.PresModel
