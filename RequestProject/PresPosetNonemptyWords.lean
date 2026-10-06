import RequestProject.PresPosetAlpha

namespace FiniteChains.PresModel
universe u
variable {α J : Type u}

/-- Nonempty attaching-word representatives, using a cancelling pair. -/
noncomputable def presNonemptyWords (ρ : J → FreeGroup α) (a : α) (j : J) :
    List (α × Bool) := presWords ρ j ++ [(a, true), (a, false)]

theorem presNonemptyWords_ne_nil (ρ : J → FreeGroup α) (a : α) (j : J) :
    presNonemptyWords ρ a j ≠ [] := by
  simp [presNonemptyWords]

theorem mk_presNonemptyWords (ρ : J → FreeGroup α) (a : α) (j : J) :
    FreeGroup.mk (presNonemptyWords ρ a j) = ρ j := by
  have hc : FreeGroup.mk [(a, true), (a, false)] = (1 : FreeGroup α) := by
    change FreeGroup.of a * (FreeGroup.of a)⁻¹ = 1
    exact mul_inv_cancel _
  rw [presNonemptyWords, ← FreeGroup.mul_mk, hc, mul_one, mk_presWords]

end FiniteChains.PresModel
