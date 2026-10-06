import RequestProject.NamedPresentation
import RequestProject.FoxNaturality
import RequestProject.PresentationDictionary

/-! The actual Fox matrix after adjoining names for the marked words. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.NamedPresentation
variable {α J I : Type} [DecidableEq α] [DecidableEq I]
  (ρ : J → FreeGroup α) (w : I → FreeGroup α)

noncomputable def wordCoefficientMap :
    FreeGroupRing α →+* MonoidAlgebra ℤ (PresGroup (rel ρ w)) :=
  (quotRingHom ℤ (relSub (rel ρ w))).comp (freeRingMap Sum.inl)

theorem matrix_internal_relator (a : α) (j : J) :
    foxMatrixPres (rel ρ w) (Sum.inl a) (Sum.inl j) =
      wordCoefficientMap ρ w (fox a (ρ j)) := by
  change quotRingHom ℤ _ (fox (Sum.inl a) (FreeGroup.map Sum.inl (ρ j))) = _
  rw [fox_map Sum.inl Sum.inl_injective]
  rfl

theorem matrix_marked_relator (i : I) (j : J) :
    foxMatrixPres (rel ρ w) (Sum.inr i) (Sum.inl j) = 0 := by
  change quotRingHom ℤ _ (fox (Sum.inr i) (FreeGroup.map Sum.inl (ρ j))) = 0
  rw [fox_map_of_not_mem_range Sum.inl (fun _ => Sum.inr_ne_inl), map_zero]

theorem matrix_internal_name (a : α) (i : I) :
    foxMatrixPres (rel ρ w) (Sum.inl a) (Sum.inr i) =
      -wordCoefficientMap ρ w (fox a (w i)) := by
  have hf : fox (Sum.inl a) (rel ρ w (Sum.inr i)) =
      -(grp (rel ρ w (Sum.inr i)) * freeRingMap Sum.inl (fox a (w i))) := by
    change fox (Sum.inl a) (FreeGroup.of (Sum.inr i) * (FreeGroup.map Sum.inl (w i))⁻¹) = _
    rw [fox_mul, fox_of, if_neg Sum.inl_ne_inr, zero_add, fox_inv,
      fox_map Sum.inl Sum.inl_injective, mul_neg, ← mul_assoc, ← grp_mul]
    rfl
  have hg : quotRingHom ℤ (relSub (rel ρ w)) (grp (rel ρ w (Sum.inr i))) = 1 := by
    have he : (QuotientGroup.mk (rel ρ w (Sum.inr i)) : PresGroup (rel ρ w)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨Sum.inr i, rfl⟩)
    change quotRingHom ℤ _ (MonoidAlgebra.single _ 1) = _
    rw [quotRingHom_single, he]
    rfl
  rw [foxMatrixPres, hf, map_neg, map_mul, hg, one_mul]
  rfl

theorem matrix_marked_name (i k : I) :
    foxMatrixPres (rel ρ w) (Sum.inr i) (Sum.inr k) = if i = k then 1 else 0 := by
  have hz : fox (Sum.inr i) (FreeGroup.map Sum.inl (w k)) = 0 :=
    fox_map_of_not_mem_range Sum.inl (fun _ => Sum.inr_ne_inl) _
  by_cases h : i = k
  · subst k
    simp [foxMatrixPres, rel, fox_mul, fox_inv, hz]
  · simp [foxMatrixPres, rel, fox_mul, fox_inv, hz, h]

end FiniteChains.NamedPresentation
