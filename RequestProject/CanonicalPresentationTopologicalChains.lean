import RequestProject.PresentationWordTopologicalChains

namespace FiniteChains.PresModel
open Comb
variable {α J : ℕ → Type}

/-- Carry the chosen padding generator along the given generator inclusions. -/
def presentationMarkedGenerator (f : ∀ i, α i ↪ α (i + 1)) (a : α 0) : ∀ i, α i
  | 0 => a
  | i + 1 => f i (presentationMarkedGenerator f a i)

variable [∀ i, DecidableEq (α i)]
  (ρ : ∀ i, J i → FreeGroup (α i))
  (f : ∀ i, α i ↪ α (i + 1)) (g : ∀ i, J i ↪ J (i + 1))
  (hr : ∀ i j, ρ (i + 1) (g i j) = FreeGroup.map (f i) (ρ i j)) (a : α 0)

/-- All nonempty word representatives and their literal compatibility are
derived from the labelled group presentations, simultaneously at every stage. -/
def canonicalPresentationStep (i : ℕ) :
    PresWordEmbedding (presCanonicalWords (ρ i) (presentationMarkedGenerator f a i))
      (presCanonicalWords (ρ (i + 1)) (presentationMarkedGenerator f a (i + 1))) :=
  canonicalPresWordEmbedding (ρ i) (ρ (i + 1)) (f i) (g i) (hr i)
    (presentationMarkedGenerator f a i)

/-- The algebraic presentation-chain hypotheses imply the exact topological
HasChain for the canonical initial model, with actual finite ambient cells
whenever the final presentation is finite. No topological comparison is assumed. -/
theorem canonical_hasChain_of_presentations (n : ℕ)
    (hp : ∀ i, i < n → (∃ b : α (i + 1), b ∉ Set.range (f i)) ∨
      ∃ j : J (i + 1), j ∉ Set.range (g i))
    (hz : ∀ i, i < n → ∀ c : PresGroup (ρ i) × J i →₀ ℤ,
      Comb.bdry2 (univCover (ρ i)) c = 0 →
      Finsupp.mapDomain (Prod.map (presInclGroupHom (f i) (ρ i) (ρ (i + 1))
        (g i) (hr i)) (g i)) c = 0)
    (finite : Bool) (hfin : finite = true → Finite (α n) ∧ Finite (J n)) :
    Whitehead.HasChain (validPresTwoComplex (presCanonicalWords (ρ 0) a)
      (presCanonicalWords_ne_nil (ρ 0) a)) n finite :=
  valid_hasChain_of_word_embeddings
    (fun i => presCanonicalWords (ρ i) (presentationMarkedGenerator f a i))
    (canonicalPresentationStep ρ f g hr a) ρ
    (fun i => mk_presCanonicalWords (ρ i) (presentationMarkedGenerator f a i))
    (fun i => presCanonicalWords_positive (ρ i) (presentationMarkedGenerator f a i))
    n hp hz finite hfin

end FiniteChains.PresModel
