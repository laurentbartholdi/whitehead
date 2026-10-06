module

public import RequestProject.CanonicalPresentationTopologicalChains
public import RequestProject.AsphericalChains

@[expose] public section

namespace FiniteChains.PresModel
open Comb
variable {α J : Type} [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
  (ρ : J → FreeGroup α) (a : α)

/-- Cancelling generator/relator pairs construct actual finite CW chains of
every length for a finite presentation with zero Fox-cycle module. This is
the precise HasChain of Challenge, with preserved original open cells. -/
theorem canonical_aspherical_hasFiniteChain (hρ : Aspherical ρ) (n : ℕ) :
    Whitehead.HasChain (validPresTwoComplex (presCanonicalWords ρ a)
      (presCanonicalWords_ne_nil ρ a)) n true := by
  let f (i : ℕ) : optIter α i ↪ optIter α (i + 1) :=
    ⟨Option.some, Option.some_injective _⟩
  let g (i : ℕ) : optIter J i ↪ optIter J (i + 1) :=
    ⟨Option.some, Option.some_injective _⟩
  apply canonical_hasChain_of_presentations (iterCancel ρ) f g
    (iterCancel_succ_some ρ) a n ?_ ?_ true ?_
  · intro i _
    left
    refine ⟨none, ?_⟩
    rintro ⟨b, hb⟩
    cases hb
  · intro i _ c hc
    have hz := zeroPi2_presInclHom_of_aspherical (aspherical_iterCancel hρ i)
      Option.some (Option.some_injective _) Option.some (iterCancel_succ_some ρ i)
    exact (zeroPi2_presInclHom_iff (iterCancel ρ i) Option.some
      (Option.some_injective _) Option.some (iterCancel_succ_some ρ i)).mp hz c hc
  · intro _
    exact ⟨inferInstance, inferInstance⟩

end FiniteChains.PresModel
