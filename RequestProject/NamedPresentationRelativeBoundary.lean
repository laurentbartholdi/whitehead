import RequestProject.NamedPresentationFoxMatrix

/-! Exact relative Fox coordinates over an arbitrary receiving group ring. -/
namespace FiniteChains.NamedPresentation
variable {α J I G : Type} [DecidableEq α] [DecidableEq I] [Fintype J] [Fintype I]
  [Group G] (ρ : J → FreeGroup α) (w : I → FreeGroup α)
  (φ : PresGroup (rel ρ w) →* G)

noncomputable def receivedWordCoefficientMap : FreeGroupRing α →+* MonoidAlgebra ℤ G :=
  (MonoidAlgebra.mapDomainRingHom ℤ φ).comp (wordCoefficientMap ρ w)

noncomputable def receivedFoxBoundary (β : J ⊕ I → MonoidAlgebra ℤ G)
    (g : α ⊕ I) : MonoidAlgebra ℤ G :=
  ∑ m, β m * MonoidAlgebra.mapDomainRingHom ℤ φ (foxMatrixPres (rel ρ w) g m)

/-- The marking coordinates are exactly the coefficients of the name relators. -/
theorem receivedFoxBoundary_marked (β : J ⊕ I → MonoidAlgebra ℤ G) (i : I) :
    receivedFoxBoundary ρ w φ β (Sum.inr i) = β (Sum.inr i) := by
  classical
  simp [receivedFoxBoundary, Fintype.sum_sum_type, matrix_marked_relator,
    matrix_marked_name, apply_ite]

/-- Vanishing at the internal generators is an equality between the old
two-boundary and the chain of the marked word paths, not an absolute cycle. -/
theorem receivedFoxBoundary_internal (β : J ⊕ I → MonoidAlgebra ℤ G) (a : α) :
    receivedFoxBoundary ρ w φ β (Sum.inl a) =
      (∑ j, β (Sum.inl j) * receivedWordCoefficientMap ρ w φ (fox a (ρ j))) -
      ∑ i, β (Sum.inr i) * receivedWordCoefficientMap ρ w φ (fox a (w i)) := by
  classical
  rw [receivedFoxBoundary, Fintype.sum_sum_type]
  simp only [matrix_internal_relator, matrix_internal_name, map_neg, mul_neg,
    Finset.sum_neg_distrib, sub_eq_add_neg]
  rfl

theorem receivedFoxBoundary_internal_zero_iff (β : J ⊕ I → MonoidAlgebra ℤ G) :
    (∀ a, receivedFoxBoundary ρ w φ β (Sum.inl a) = 0) ↔
      ∀ a, (∑ j, β (Sum.inl j) * receivedWordCoefficientMap ρ w φ (fox a (ρ j))) =
        ∑ i, β (Sum.inr i) * receivedWordCoefficientMap ρ w φ (fox a (w i)) := by
  simp only [receivedFoxBoundary_internal, sub_eq_zero]

end FiniteChains.NamedPresentation
