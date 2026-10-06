module

public import RequestProject.OrderNerveRealizationSimplices
public import RequestProject.OrderNerveDimension

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory Simplicial

/-- Nondegenerate simplices alone cover the actual geometric realization. -/
theorem orderNerveRealization_nonDegenerate_jointly_surjective (P : Type) [PartialOrder P]
    (x : orderNerveRealization P) :
    ∃ (n : ℕ) (s : (nerve P).nonDegenerate n)
      (z : SimplexCategory.toTop.obj ⦋n⦌), orderNerveRealizationSimplex P s.val z = x := by
  obtain ⟨n, s, z, hz⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  induction n using SimplexCategory.rec with | _ n =>
    obtain ⟨m, a, _, t, ht⟩ := (nerve P).exists_nonDegenerate s
    refine ⟨m, t, SimplexCategory.toTop.map a z, ?_⟩
    have h := congrArg (fun k => k z) (orderNerveRealizationSimplex_operator P a t.val)
    change orderNerveRealizationSimplex P t.val (SimplexCategory.toTop.map a z) =
      orderNerveRealizationSimplex P ((nerve P).map a.op t.val) z at h
    rw [← ht] at h
    exact h.trans hz

/-- The actual realization of a bounded ranked poset is covered by simplices of
bounded dimension, without adding any topological comparison premise. -/
theorem orderNerveRealization_bounded_simplex_cover (P : Type) [PartialOrder P]
    (rank : P → ℕ) (hrank : StrictMono rank) (d : ℕ) (hbound : ∀ p, rank p ≤ d)
    (x : orderNerveRealization P) :
    ∃ (n : ℕ) (_ : n ≤ d) (s : (nerve P).nonDegenerate n)
      (z : SimplexCategory.toTop.obj ⦋n⦌), orderNerveRealizationSimplex P s.val z = x := by
  obtain ⟨n, s, z, hz⟩ := orderNerveRealization_nonDegenerate_jointly_surjective P x
  exact ⟨n, orderNerve_nonDegenerate_dimension_le rank hrank d hbound s.val s.property,
    s, z, hz⟩

/-- Continuity is detected by the nondegenerate realization simplices alone. -/
theorem orderNerveRealization_nonDegenerate_continuous_iff (P : Type) [PartialOrder P]
    {X : Type*} [TopologicalSpace X] (f : orderNerveRealization P → X) :
    Continuous f ↔ ∀ (n : ℕ) (s : (nerve P).nonDegenerate n),
      Continuous (f ∘ orderNerveRealizationSimplex P s.val) := by
  constructor
  · intro h n s
    exact h.comp (orderNerveRealizationSimplex P s.val).hom.continuous
  · intro h
    apply (orderNerveRealization_continuous_iff P f).mpr
    intro n s
    induction n using SimplexCategory.rec with | _ n =>
      obtain ⟨m, a, _, t, ht⟩ := (nerve P).exists_nonDegenerate s
      have hc := (h m t).comp (SimplexCategory.toTop.map a).hom.continuous
      convert hc using 1
      funext z
      have ha := congrArg (fun k => k z) (orderNerveRealizationSimplex_operator P a t.val)
      change orderNerveRealizationSimplex P t.val (SimplexCategory.toTop.map a z) =
        orderNerveRealizationSimplex P ((nerve P).map a.op t.val) z at ha
      rw [← ht] at ha
      exact congrArg f ha.symm

end FiniteChains.Comb
