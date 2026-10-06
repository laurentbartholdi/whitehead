import RequestProject.PresWordEmbeddingPi1
import RequestProject.PresWordEmbeddingTopology
import RequestProject.PresFiniteTopologicalCockcroft
import RequestProject.InitialComplex
import RequestProject.OrderPi1TrivialLift
import RequestProject.OrderEmbeddingOneChain

namespace FiniteChains.PresModel
open Comb
variable {I J : Type} [LinearOrder I] [Fintype I] [DecidableEq I]
  [Fintype J]
variable (r : J → FreeGroup I) (a : I)

/-- The initial pair retains the old generators, old labelled two-cells and their
literal canonical attaching words in the finite valid-position model. -/
def initialWordEmbedding :
    PresWordEmbedding (presCanonicalWords r a) (presCanonicalWords (relY r) (Sum.inl a)) :=
  canonicalPresWordEmbedding r (relY r) ⟨Sum.inl, Sum.inl_injective⟩
    ⟨Sum.inl, Sum.inl_injective⟩ (fun _ => rfl) a

omit [Fintype I] [Fintype J] in
theorem initial_valid_pi1Trivial (hMs : ExpSurjective r) :
    Pi1Trivial (orderCxMap (initialWordEmbedding r a).validMap
      (initialWordEmbedding r a).validMap.monotone) := by
  apply (initialWordEmbedding r a).pi1Trivial_validMap_of_generators (relY r)
    (mk_presCanonicalWords (relY r) (Sum.inl a)) (presCanonicalWords_positive r a)
  intro i
  exact xEl_eq_one hMs i

omit [Fintype I] in
/-- The original Fox argument now proves that the actual continuous inclusion
in the finite initial pair kills every based topological two-sphere. -/
theorem initial_valid_killsPi2 (hMs : ExpSurjective r) (hMi : ExpInjective r) :
    Whitehead.KillsPi2 (initialWordEmbedding r a).validRealizationMap := by
  apply killsPi2_orderRealization_of_isCockcroft_of_pi1Trivial
    (initialWordEmbedding r a).validMap (initialWordEmbedding r a).validMap.monotone
    (validPresPos_isConnected _ (presCanonicalWords_ne_nil r a))
    (validPresBase (presCanonicalWords r a)) (initial_valid_pi1Trivial r a hMs)
  exact validPresRealization_isCockcroft_of_fox r (presCanonicalWords r a)
    (mk_presCanonicalWords r a) (presCanonicalWords_positive r a)
    (isCockcroft_of_expInjective r hMi)

theorem initial_valid_target_isCockcroft (hMs : ExpSurjective r) (hMi : ExpInjective r) :
    Whitehead.IsCockcroft (orderNerveRealization
      (ValidPresPos (presCanonicalWords (relY r) (Sum.inl a)))) :=
  validPresRealization_isCockcroft_of_fox (relY r) (presCanonicalWords (relY r) (Sum.inl a))
    (mk_presCanonicalWords (relY r) (Sum.inl a))
    (presCanonicalWords_positive (relY r) (Sum.inl a)) (isCockcroft_relY hMs hMi)

omit [Fintype I] [Fintype J] in
theorem initial_valid_proper : ∃ p,
    p ∉ Set.range (initialWordEmbedding r a).validMap := by
  refine ⟨⟨iRose _ (.mid (Sum.inr (a, false))), trivial⟩, ?_⟩
  apply (initialWordEmbedding r a).valid_mid_not_mem_range
  rintro ⟨b, he⟩
  cases he

/-- The exact finite one-step clause of Challenge for an acyclic finite
presentation with a chosen generator. No pi2 comparison assumption remains. -/
theorem initial_valid_hasChain_one (hMs : ExpSurjective r) (hMi : ExpInjective r) :
    Whitehead.HasChain (validPresTwoComplex (presCanonicalWords r a)
      (presCanonicalWords_ne_nil r a)) 1 true :=
  orderNerve_hasChain_one_of_embedding (initialWordEmbedding r a).validMap
    (validPresPos_isConnected _ (presCanonicalWords_ne_nil r a))
    (validPresPos_isConnected _ (presCanonicalWords_ne_nil (relY r) (Sum.inl a)))
    (initial_valid_proper r a) (initial_valid_killsPi2 r a hMs hMi) true
    (fun _ => inferInstance)

end FiniteChains.PresModel
