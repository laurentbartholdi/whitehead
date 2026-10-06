import RequestProject.OrderRealizationPi2Criterion
import RequestProject.OrderUniversalPosetThree
import RequestProject.OrderUniversalTetLift

namespace FiniteChains.Comb
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

/-- The genuine pi2 criterion in the path-cover coordinates used by the
chamber's finite equivariant generation theorem. -/
theorem killsPi2_orderRealization_iff_pathCover_cycles_bound
    (f : P → Q) (hf : Monotone f) (a : P)
    (hP : IsConnected (orderCx P)) (hQ : IsConnected (orderCx Q)) :
    Whitehead.KillsPi2
      ⟨orderNerveRealizationMap f hf, (orderNerveRealizationMap f hf).hom.continuous⟩ ↔
      ∀ (c : UF (orderCx P) a →₀ ℤ), bdry2 (uCover (orderCx P) a) c = 0 →
        ∃ b : UOrdTet Q (f a) →₀ ℤ, uOrdBoundary3 b =
          chain2 (univLift (orderCx P) (orderCxMap f hf) a) c := by
  rw [killsPi2_orderRealization_iff_universal_cycles_bound f hf a hP hQ]
  constructor
  · intro hk c hc
    obtain ⟨d, hd, _⟩ := exists_unique_uOrder_cycle c hc
    obtain ⟨b, hb⟩ := hk d hd.2
    refine ⟨Finsupp.mapDomain uOrderTet b, ?_⟩
    rw [← uOrderHom_ordBoundary3, hb, uOrderMap_chain2, hd.1]
  · intro hk c hc
    obtain ⟨b, hb⟩ := hk (chain2 uOrderHom c) ((uOrderHom_cycle_iff c).mpr hc)
    obtain ⟨d, hd⟩ := exists_uOrder_three_chain b
    refine ⟨d, ?_⟩
    apply uOrderHom_chain2_injective (P := Q) (a := f a)
    rw [uOrderHom_ordBoundary3, hd, hb, uOrderMap_chain2]

end FiniteChains.Comb
