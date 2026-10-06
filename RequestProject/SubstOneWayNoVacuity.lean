import RequestProject.SubstOneWay
import RequestProject.SubstHomFNotInjective

/-!
# The block maps are a genuine geometric input

The one-way comparison of `RequestProject/SubstOneWay.lean` derives the injectivity of
`FiniteChains.BlockFamily.substHomF` from the existence of the marked block maps
`FiniteChains.BlockFamily.BlockMaps` over an injective homomorphism `j`.  This file records that
this input is not for free: for the substitution of
`RequestProject/SubstHomFNotInjective.lean`, whose structural homomorphism is not injective,
**no** family of marked block maps exists over any injective `j`, whatever the receiving group.

So the data required by the one-way comparison is exactly as strong as it must be: it is the
place where the geometry of the blocks enters, and the conclusion of the comparison is not
vacuous.
-/

namespace FiniteChains
namespace BlockFamily

universe u v

/-- **No marked block maps for a substitution which is not injective.**  For the substitution
`⟨a ∣ 1⟩ → ⟨a ∣ a⟩` there is no family of marked block maps over an injective homomorphism. -/
theorem no_blockMaps_example {H : Type v} [Group H] (j : PresGroup exRho.{u} →* H)
    (hj : Function.Injective j) (B : BlockMaps exRho.{u} exBsub.{u} j) : False := by
  have h1 : B.b PUnit.unit (FreeGroup.of (Sum.inl PUnit.unit)) = 1 := B.rel PUnit.unit PUnit.unit
  rw [B.mark PUnit.unit PUnit.unit] at h1
  exact exClass_ne_one.{u} (hj (by rw [h1, map_one]))

end BlockFamily
end FiniteChains
