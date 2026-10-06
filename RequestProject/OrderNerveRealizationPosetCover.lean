import RequestProject.OrderNerveRealizationNestedSubcomplex
import RequestProject.PosetCoverUpTransform

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

namespace IsPosetCover
variable {P Q : Type} [PartialOrder P] [PartialOrder Q] {f : P → Q}

/-- A poset cover reflects order in every common upper interval. -/
theorem le_of_le_above (hf : IsPosetCover f) {a b v : P}
    (ha : v ≤ a) (hb : v ≤ b) (h : f a ≤ f b) : a ≤ b := by
  obtain ⟨c, ⟨hac, hfc⟩, _⟩ := hf.up a (f b) h
  have hc : c = b := hf.up_inj (ha.trans hac) hb hfc
  exact hc ▸ hac

/-- Every actual simplex has an actual simplex lift through a poset cover. -/
theorem exists_simplex_lift (hf : IsPosetCover f) {n : SimplexCategory}
    (s : (nerve Q).obj (Opposite.op n)) :
    ∃ t : (nerve P).obj (Opposite.op n), (nerveMap hf.mono.functor).app _ t = s := by
  obtain ⟨a, ha⟩ := hf.surj (s.obj 0)
  have hu : ∀ i, ∃ b, a ≤ b ∧ f b = s.obj i := by
    intro i
    have hi : f a ≤ s.obj i := by
      rw [ha]
      exact leOfHom (s.map (homOfLE (Fin.zero_le i)))
    obtain ⟨b, hb, _⟩ := hf.up a (s.obj i) hi
    exact ⟨b, hb⟩
  choose b hb hfb using hu
  let t : (nerve P).obj (Opposite.op n) :=
    { obj := b
      map := fun h => homOfLE (hf.le_of_le_above (hb _) (hb _) (by
        rw [hfb, hfb]
        exact leOfHom (s.map h))) }
  refine ⟨t, ?_⟩
  exact CategoryTheory.Functor.ext hfb

/-- The actual realized map of a poset cover is surjective. -/
theorem realizationMap_surjective (hf : IsPosetCover f) :
    Function.Surjective (orderNerveRealizationMap f hf.mono) := by
  intro x
  obtain ⟨n, s, z, hx⟩ := orderNerveRealizationSimplex_jointly_surjective Q x
  obtain ⟨t, ht⟩ := hf.exists_simplex_lift s
  refine ⟨orderNerveRealizationSimplex P t z, ?_⟩
  have he := congrArg (fun k => k z) (orderNerveRealizationSimplex_natural f hf.mono t)
  change orderNerveRealizationMap f hf.mono (orderNerveRealizationSimplex P t z) =
    orderNerveRealizationSimplex Q ((nerveMap hf.mono.functor).app _ t) z at he
  rw [ht] at he
  exact he.trans hx

end IsPosetCover
end FiniteChains.Comb
