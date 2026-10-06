import RequestProject.OrderUniversalCocycleReading
import RequestProject.OrderUniversalPoset

namespace FiniteChains.Comb.OrdCocycle
universe u v
variable {P : Type u} [PartialOrder P] {G : Type v} [Group G]
  (c : OrdCocycle P G) (a : P)

/-- Actual upward edge lifting multiplies actual vertex reading by the actual cocycle value. -/
theorem readVertex_uOrderStep (p : UOrder P a) (q : P) (h : uOrderEnd p ≤ q) :
    c.readVertex a (uOrderStep p q h) = c.readVertex a p * c.val (uOrderEnd p) q :=
  c.readVertex_extend a (ordPos h) p rfl

/-- Comparable actual universal-cover vertices satisfy the cocycle transport formula. -/
theorem readVertex_of_le (p q : UOrder P a) (h : p ≤ q) :
    c.readVertex a q = c.readVertex a p * c.val (uOrderEnd p) (uOrderEnd q) := by
  obtain ⟨hle, he⟩ := h
  rw [← he]
  simpa only [uOrderStep_end] using c.readVertex_uOrderStep a p (uOrderEnd q) hle

/-- Reading down a genuine lifted comparability multiplies by the inverse cocycle value. -/
theorem readVertex_lower_of_le (p q : UOrder P a) (h : p ≤ q) :
    c.readVertex a p = c.readVertex a q * (c.val (uOrderEnd p) (uOrderEnd q))⁻¹ := by
  rw [c.readVertex_of_le a p q h]
  simp

end FiniteChains.Comb.OrdCocycle
