import RequestProject.OrderComplexPi1Transfer

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [Preorder P] [Preorder Q]

/-- An actual order isomorphism is surjective on based fundamental groups. -/
theorem orderIso_pi1_surjective (e : P ≃o Q) (a : P) :
    Function.Surjective (pi1Map (orderCxMap e e.monotone) a) := by
  intro z
  induction z using Quotient.inductionOn with
  | h p =>
    have hp : IsPath (orderCx P).src (orderCx P).tgt
        (mapPath (orderCxMap e.symm e.symm.monotone) p.val) a a := by
      simpa only [orderCxMap, e.symm_apply_apply] using
        isPath_mapPath (orderCxMap e.symm e.symm.monotone) p.property
    refine ⟨Pi1.mk ⟨_, hp⟩, Quotient.sound ?_⟩
    change Htpy (orderCx Q) (e a) (e a)
      (mapPath (orderCxMap e e.monotone)
        (mapPath (orderCxMap e.symm e.symm.monotone) p.val)) p.val
    rw [mapPath_comp_eq_self e.symm.monotone e.monotone e.apply_symm_apply]
    exact Htpy.refl _

end FiniteChains.Comb
