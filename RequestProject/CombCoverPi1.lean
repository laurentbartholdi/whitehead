import RequestProject.CombCoveringLift
import RequestProject.CombPresPi1
import RequestProject.CoverComplex

/-!
# The cover attached to `Ñ` realises the subgroup `Ñ/R` of `π₁`

`RequestProject/CoverComplex.lean` builds, for a normal subgroup `Ñ ◁ F` containing the
relators, the covering `K_Ñ → K` of the presentation complex with deck group `F/Ñ`, and proves
that it is a connected regular covering.  Now that the fundamental group of `K` has been
computed (`RequestProject/CombPresPi1.lean`) and that paths lift uniquely along a covering
(`RequestProject/CombCoveringLift.lean`), one can say *which* covering it is:

`FiniteChains.Comb.range_pi1Map_coverProj` — the image of `π₁(K_Ñ)` in
`π₁(K) = F/R` is exactly `Ñ/R`.

Together with `FiniteChains.Comb.pi1Map_injective_of_isCovering` this identifies
`π₁(K_Ñ)` with `Ñ/R`.
-/

namespace FiniteChains
namespace Comb

universe u

variable {α : Type u} [DecidableEq α] {J : Type u}
variable {Nsub : Subgroup (FreeGroup α)} [Nsub.Normal] {ρ : J → FreeGroup α}
variable (hρ : ∀ j, ρ j ∈ Nsub)

/-- The word spelled by the projection of an edge path of the cover. -/
def coverWord (m : List (((FreeGroup α ⧸ Nsub) × α) × Bool)) : List (α × Bool) :=
  mapPath (coverProj hρ) m

theorem mapPath_liftPath (L : List (α × Bool)) (q : FreeGroup α ⧸ Nsub) :
    coverWord hρ (liftPath L q) = L := map_liftPath L q

/-- An edge path of the cover **is** the lift of the word it spells, and its terminal vertex
is the initial one translated by that word. -/
theorem eq_liftPath_of_isPath {m : List (((FreeGroup α ⧸ Nsub) × α) × Bool)}
    {q q' : FreeGroup α ⧸ Nsub}
    (hm : IsPath (coverComplex Nsub ρ hρ).src (coverComplex Nsub ρ hρ).tgt m q q') :
    m = liftPath (coverWord hρ m) q ∧
      q' = q * QuotientGroup.mk (FreeGroup.mk (coverWord hρ m)) := by
  have hlift : IsPath (coverComplex Nsub ρ hρ).src (coverComplex Nsub ρ hρ).tgt
      (liftPath (coverWord hρ m) q) q (q * QuotientGroup.mk (FreeGroup.mk (coverWord hρ m))) :=
    liftPath_isPath Nsub (coverWord hρ m) q
  have hmaps : mapPath (coverProj hρ) m
      = mapPath (coverProj hρ) (liftPath (coverWord hρ m) q) := by
    rw [show mapPath (coverProj hρ) (liftPath (coverWord hρ m) q) = coverWord hρ m from
      mapPath_liftPath hρ _ q]
    rfl
  have heq : m = liftPath (coverWord hρ m) q :=
    liftPath_unique (coverProj_isCovering hρ) m (liftPath (coverWord hρ m) q) q q' _ hm hlift hmaps
  refine ⟨heq, ?_⟩
  exact isPath_endpoint_eq (heq ▸ hm) hlift

/-- **The covering attached to `Ñ` realises the subgroup `Ñ/R`**: the image of the
fundamental group of the cover in `π₁(K) = F/R` is the image of `Ñ`. -/
theorem range_pi1Map_coverProj :
    MonoidHom.range (((pi1PresEquiv ρ).toMonoidHom).comp
        (pi1Map (coverProj hρ) (1 : FreeGroup α ⧸ Nsub)))
      = Nsub.map (QuotientGroup.mk' (relSub ρ)) := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    induction g using Quotient.inductionOn with
    | h m =>
        obtain ⟨m, hm⟩ := m
        obtain ⟨-, hend⟩ := eq_liftPath_of_isPath hρ hm
        have hone : (QuotientGroup.mk (FreeGroup.mk (coverWord hρ m)) :
            FreeGroup α ⧸ Nsub) = 1 := by
          have := hend.symm
          rwa [one_mul] at this
        have hmem : FreeGroup.mk (coverWord hρ m) ∈ Nsub :=
          (QuotientGroup.eq_one_iff _).mp hone
        show (QuotientGroup.mk (FreeGroup.mk (coverWord hρ m)) : PresGroup ρ) ∈
          Subgroup.map (QuotientGroup.mk' (relSub ρ)) Nsub
        exact Subgroup.mem_map_of_mem _ hmem
  · rintro ⟨n, hn, rfl⟩
    have hpath := liftPath_isPath Nsub (FreeGroup.toWord n) (1 : FreeGroup α ⧸ Nsub)
    rw [FreeGroup.mk_toWord, (QuotientGroup.eq_one_iff n).2 hn, mul_one] at hpath
    refine ⟨Pi1.mk ⟨liftPath (FreeGroup.toWord n) 1, hpath⟩, ?_⟩
    show QuotientGroup.mk (FreeGroup.mk (coverWord hρ (liftPath (FreeGroup.toWord n) 1)))
      = QuotientGroup.mk' (relSub ρ) n
    rw [mapPath_liftPath hρ (FreeGroup.toWord n) 1, FreeGroup.mk_toWord]
    rfl

end Comb
end FiniteChains
