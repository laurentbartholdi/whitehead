import RequestProject.FoxNaturality
import RequestProject.SubstOneWay

/-! Fox coordinates retained by a word substitution. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

variable {α β : Type*}

theorem groupRingMap_grp (φ : FreeGroup α →* FreeGroup β) (w : FreeGroup α) :
    MonoidAlgebra.mapDomainRingHom ℤ φ (grp w) = grp (φ w) := by
  change MonoidAlgebra.mapDomain φ (MonoidAlgebra.single w 1) = MonoidAlgebra.single (φ w) 1
  exact MonoidAlgebra.mapDomain_single

/-- A coordinate of a Fox derivative is preserved when the substituted
generators have the corresponding Kronecker derivatives. -/
theorem fox_subst_coordinate [DecidableEq α] [DecidableEq β]
    (φ : FreeGroup α →* FreeGroup β) (a : α) (b : β)
    (h : ∀ i, fox b (φ (FreeGroup.of i)) = if a = i then 1 else 0)
    (w : FreeGroup α) :
    fox b (φ w) = MonoidAlgebra.mapDomainRingHom ℤ φ (fox a w) := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of i => rw [h, fox_of]; split_ifs <;> simp
  | inv_of i ih =>
      rw [map_inv, fox_inv, fox_inv, map_neg, map_mul, ih, groupRingMap_grp, map_inv]
  | mul u v hu hv =>
      rw [map_mul, fox_mul, fox_mul, map_add, hu, hv, map_mul, groupRingMap_grp]

namespace BlockFamily
universe u
variable {A S : Type u} {I Z : S → Type u}
  [DecidableEq A] [∀ s, DecidableEq (I s)] [∀ s, DecidableEq (Z s)]

/-- Substituting arbitrary old words for the markings retains every internal
Fox coordinate, before taking a quotient or an augmentation. -/
theorem fox_blockSubst_internal (u : ∀ s, I s → FreeGroup A) (s : S)
    (z : Z s) (w : FreeGroup (I s ⊕ Z s)) :
    fox (Sum.inr z) (blockSubst u s w) =
      MonoidAlgebra.mapDomainRingHom ℤ (blockSubst u s) (fox (Sum.inr z) w) := by
  apply fox_subst_coordinate
  rintro (i | z')
  · rw [blockSubst_of_inl,
      fox_map_of_not_mem_range Sum.inl (fun _ => Sum.inr_ne_inl)]
    simp
  · simp only [blockSubst_of_inr, fox_of, Sum.inr.injEq]

end BlockFamily
end FiniteChains
