import RequestProject.PresWordEmbeddingCombPi2
import RequestProject.OrderEmbeddingOneChain

namespace FiniteChains.PresModel
open Comb
variable {α β J K : Type} [DecidableEq α] [DecidableEq β]
  (ρ : J → FreeGroup α) (σ : K → FreeGroup β)
  (f : α ↪ β) (g : J ↪ K) (hg : ∀ j, σ (g j) = FreeGroup.map f (ρ j)) (a : α)

/-- A cycle calculation in the original algebraic universal cover proves
actual topological pi2 vanishing for the canonical labelled inclusion. -/
theorem canonical_valid_killsPi2_of_univCover
    (hz : ∀ c : PresGroup ρ × J →₀ ℤ, Comb.bdry2 (univCover ρ) c = 0 →
      Finsupp.mapDomain (Prod.map (presInclGroupHom f ρ σ g hg) g) c = 0) :
    Whitehead.KillsPi2 (canonicalPresWordEmbedding ρ σ f g hg a).validRealizationMap := by
  apply (canonicalPresWordEmbedding ρ σ f g hg a).valid_killsPi2_of_full
  apply ((canonicalPresWordEmbedding ρ σ f g hg a).killsPi2_iff_univCover
    (presCanonicalWords_positive ρ a) (presCanonicalWords_positive σ (f a))
    ρ σ (mk_presCanonicalWords ρ a) (mk_presCanonicalWords σ (f a))).mpr
  exact hz

/-- New generator or relator labels give an actual missing point of the
canonical valid-position inclusion. -/
theorem canonical_valid_proper
    (hp : (∃ b : β, b ∉ Set.range f) ∨ ∃ k : K, k ∉ Set.range g) :
    ∃ p, p ∉ Set.range (canonicalPresWordEmbedding ρ σ f g hg a).validMap := by
  rcases hp with ⟨b, hb⟩ | ⟨k, hk⟩
  · exact ⟨⟨iRose _ (.mid b), trivial⟩,
      (canonicalPresWordEmbedding ρ σ f g hg a).valid_mid_not_mem_range hb⟩
  · exact ⟨⟨apexOf _ k, trivial⟩,
      (canonicalPresWordEmbedding ρ σ f g hg a).valid_apex_not_mem_range hk⟩

/-- An algebraic labelled presentation extension gives the exact one-step
topological chain of Challenge, including properness, preserved original
open cells, and finite ambient cells when requested. -/
theorem canonical_hasChain_one_of_univCover
    (hp : (∃ b : β, b ∉ Set.range f) ∨ ∃ k : K, k ∉ Set.range g)
    (hz : ∀ c : PresGroup ρ × J →₀ ℤ, Comb.bdry2 (univCover ρ) c = 0 →
      Finsupp.mapDomain (Prod.map (presInclGroupHom f ρ σ g hg) g) c = 0)
    (finite : Bool) (hfin : finite = true → Finite β ∧ Finite K) :
    Whitehead.HasChain (validPresTwoComplex (presCanonicalWords ρ a)
      (presCanonicalWords_ne_nil ρ a)) 1 finite := by
  apply orderNerve_hasChain_one_of_embedding (canonicalPresWordEmbedding ρ σ f g hg a).validMap
    (validPresPos_isConnected _ (presCanonicalWords_ne_nil ρ a))
    (validPresPos_isConnected _ (presCanonicalWords_ne_nil σ (f a)))
    (canonical_valid_proper ρ σ f g hg a hp)
    (canonical_valid_killsPi2_of_univCover ρ σ f g hg a hz) finite
  intro hf
  letI := (hfin hf).1
  letI := (hfin hf).2
  infer_instance

end FiniteChains.PresModel
