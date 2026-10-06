import RequestProject.OrderUniversalRealizationAcyclicity
import RequestProject.PresWordEmbeddingCombPi2
import RequestProject.AsphericalFiniteTopologicalChains

namespace FiniteChains.PresModel
open Comb
variable {α J : Type} [DecidableEq α]
  (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

include hw hpos in
/-- Vanishing of the algebraic universal-cover cycles gives zero actual pi2
of the retained valid-position presentation realization. -/
theorem validPresRealization_killsPi2_id_of_univ_cycles_zero
    (hz : ∀ c : PresGroup ρ × J →₀ ℤ, Comb.bdry2 (univCover ρ) c = 0 → c = 0) :
    Whitehead.KillsPi2 (ContinuousMap.id (orderNerveRealization (ValidPresPos w))) := by
  have hk : Whitehead.KillsPi2 (PresWordEmbedding.refl w).realizationMap := by
    apply ((PresWordEmbedding.refl w).killsPi2_iff_univCover hpos hpos ρ ρ hw hw).mpr
    intro c hc
    rw [hz c hc, Finsupp.mapDomain_zero]
  have hv := (PresWordEmbedding.refl w).valid_killsPi2_of_full hk
  rwa [PresWordEmbedding.validRealizationMap_refl] at hv

include hw hpos in
/-- This constructs the genuine connected regular acyclic topological cover
of the finite-position CW model. All comparison and covering facts are proved;
the displayed cycle hypothesis is the original algebraic input. -/
theorem validPresTwoComplex_hasAcyclicRegularCover_of_univ_cycles_zero
    (hz : ∀ c : PresGroup ρ × J →₀ ℤ, Comb.bdry2 (univCover ρ) c = 0 → c = 0) :
    Whitehead.HasAcyclicRegularCover
      (validPresTwoComplex w (fun j => List.length_pos_iff.mp (hpos j))) :=
  orderNerve_hasAcyclicRegularCover_of_killsPi2_id (validPresBase w)
    (validPresPos_isConnected w (fun j => List.length_pos_iff.mp (hpos j)))
    (validPresRealization_killsPi2_id_of_univ_cycles_zero ρ w hw hpos hz)

variable [Fintype α] [Fintype J] [DecidableEq J]

/-- The old Fox asphericity predicate now supplies an actual acyclic regular
cover of the chosen canonical finite CW model, as specified in Challenge. -/
theorem canonical_aspherical_hasAcyclicRegularCover (a : α) (hρ : Aspherical ρ) :
    Whitehead.HasAcyclicRegularCover
      (validPresTwoComplex (presCanonicalWords ρ a) (presCanonicalWords_ne_nil ρ a)) := by
  apply validPresTwoComplex_hasAcyclicRegularCover_of_univ_cycles_zero ρ
    (presCanonicalWords ρ a) (mk_presCanonicalWords ρ a) (presCanonicalWords_positive ρ a)
  intro c hc
  apply (coords (relSub ρ) J).injective
  rw [map_zero]
  exact hρ _ ((univCover_bdry2_eq_zero_iff ρ c).mp hc)

end FiniteChains.PresModel
