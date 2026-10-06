import RequestProject.OrderPosetCovering

/-! Actual interval-covering maps remain covering maps after an order isomorphism. -/
namespace FiniteChains.Comb.IsPosetCover
universe u
variable {P Q R : Type u} [Preorder P] [Preorder Q] [Preorder R]
  {f : P → Q}

theorem postcompose_orderIso (hf : IsPosetCover f) (e : Q ≃o R) :
    IsPosetCover (fun p => e (f p)) where
  mono := e.monotone.comp hf.mono
  surj := e.surjective.comp hf.surj
  up a r har := by
    have ha : f a ≤ e.symm r := by
      simpa only [OrderIso.symm_apply_apply] using e.symm.monotone har
    obtain ⟨b, ⟨hab, hfb⟩, hu⟩ := hf.up a (e.symm r) ha
    refine ⟨b, ⟨hab, by rw [hfb, e.apply_symm_apply]⟩, ?_⟩
    rintro c ⟨hac, hec⟩
    apply hu c
    exact ⟨hac, by simpa only [OrderIso.symm_apply_apply] using congrArg e.symm hec⟩
  down a r hra := by
    have ha : e.symm r ≤ f a := by
      simpa only [OrderIso.symm_apply_apply] using e.symm.monotone hra
    obtain ⟨b, ⟨hba, hfb⟩, hu⟩ := hf.down a (e.symm r) ha
    refine ⟨b, ⟨hba, by rw [hfb, e.apply_symm_apply]⟩, ?_⟩
    rintro c ⟨hca, hec⟩
    apply hu c
    exact ⟨hca, by simpa only [OrderIso.symm_apply_apply] using congrArg e.symm hec⟩

end FiniteChains.Comb.IsPosetCover
