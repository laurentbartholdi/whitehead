import RequestProject.PresPosetAlphaW

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j)

/-- The actual presentation reading homomorphism is surjective by its proved marked section. -/
theorem readingPresW_surjective : Function.Surjective (readingPresW ρ w hw) := by
  intro x
  exact ⟨alphaHomW ρ w hw x, readingPresW_alphaHomW ρ w hw x⟩

end FiniteChains.PresModel
