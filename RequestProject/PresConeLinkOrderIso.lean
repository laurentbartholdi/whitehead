import RequestProject.PresConeIntervals
import RequestProject.PosetCoverLowerInterval

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

def RelatorCircle := {x : TCirc w // x.1 = j ∧ x.2.1 < (w j).length}
instance : PartialOrder (RelatorCircle w j) := Subtype.partialOrder _

def relatorCircleToBelow (x : RelatorCircle w j) : StrictBelow (apexOf w j) :=
  ⟨iCirc w x.1, (presPos_lt_apex_iff w j _).mpr
    ⟨x.1.2.1, x.1.2.2, x.2.2, by
      rcases x with ⟨⟨j', k, t⟩, hj, hk⟩
      change j' = j at hj
      subst j'
      rfl⟩⟩

theorem relatorCircleToBelow_injective : Function.Injective (relatorCircleToBelow w j) := by
  intro a b h
  apply Subtype.ext
  exact Sum.inr.inj (Sum.inl.inj (congrArg Subtype.val h))

theorem relatorCircleToBelow_surjective : Function.Surjective (relatorCircleToBelow w j) := by
  intro p
  obtain ⟨k, t, hk, he⟩ := (presPos_lt_apex_iff w j p.1).mp p.2
  refine ⟨⟨TCirc.pt w j k t, rfl, hk⟩, ?_⟩
  exact Subtype.ext he.symm

/-- The actual lower interval of a relator apex is its valid attaching circle. -/
noncomputable def relatorCircleOrderIso : RelatorCircle w j ≃o StrictBelow (apexOf w j) where
  toEquiv := Equiv.ofBijective (relatorCircleToBelow w j)
    ⟨relatorCircleToBelow_injective w j, relatorCircleToBelow_surjective w j⟩
  map_rel_iff' := by
    intro a b
    change iCirc w a.1 ≤ iCirc w b.1 ↔ a.1 ≤ b.1
    rfl

end FiniteChains.PresModel
