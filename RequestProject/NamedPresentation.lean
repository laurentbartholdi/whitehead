import RequestProject.SurfaceWordExpansion

/-! Adjoining names for concrete words preserves a presented group. -/
namespace FiniteChains.NamedPresentation
variable {α J I : Type} (ρ : J → FreeGroup α) (w : I → FreeGroup α)

def rel : J ⊕ I → FreeGroup (α ⊕ I)
  | .inl j => FreeGroup.map Sum.inl (ρ j)
  | .inr i => FreeGroup.of (Sum.inr i) * (FreeGroup.map Sum.inl (w i))⁻¹

theorem name_eq_word (i : I) :
    (QuotientGroup.mk (FreeGroup.of (Sum.inr i)) : PresGroup (rel ρ w)) =
      QuotientGroup.mk (FreeGroup.map Sum.inl (w i)) := by
  have h : (QuotientGroup.mk
      (FreeGroup.of (Sum.inr i) * (FreeGroup.map Sum.inl (w i))⁻¹) : PresGroup (rel ρ w)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨Sum.inr i, rfl⟩)
  change (QuotientGroup.mk' (relSub (rel ρ w)))
    (FreeGroup.of (Sum.inr i) * (FreeGroup.map Sum.inl (w i))⁻¹) = 1 at h
  rw [map_mul, map_inv] at h
  exact (mul_inv_eq_one.mp h)

def inclusion : PresGroup ρ →* PresGroup (rel ρ w) :=
  QuotientGroup.lift _ ((QuotientGroup.mk' (relSub (rel ρ w))).comp (FreeGroup.map Sum.inl)) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨Sum.inl j, rfl⟩))

theorem folded_relator_eq_one (j : J ⊕ I) :
    (QuotientGroup.mk (SurfaceWordExpansion.foldNames w (rel ρ w j)) : PresGroup ρ) = 1 := by
  cases j with
  | inl j =>
    change (QuotientGroup.mk (SurfaceWordExpansion.foldNames w (FreeGroup.map Sum.inl (ρ j))) :
      PresGroup ρ) = 1
    rw [SurfaceWordExpansion.foldNames_map_inl]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨j, rfl⟩)
  | inr i =>
    change (QuotientGroup.mk' (relSub ρ))
      (SurfaceWordExpansion.foldNames w
        (FreeGroup.of (Sum.inr i) * (FreeGroup.map Sum.inl (w i))⁻¹)) = 1
    rw [map_mul, map_inv, SurfaceWordExpansion.foldNames_map_inl]
    simp [SurfaceWordExpansion.foldNames]

def elimination : PresGroup (rel ρ w) →* PresGroup ρ :=
  QuotientGroup.lift _ ((QuotientGroup.mk' (relSub ρ)).comp (SurfaceWordExpansion.foldNames w)) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    exact folded_relator_eq_one ρ w j)

theorem elimination_inclusion (g : PresGroup ρ) :
    elimination ρ w (inclusion ρ w g) = g := by
  induction g using QuotientGroup.induction_on with
  | H v =>
    change (QuotientGroup.mk (SurfaceWordExpansion.foldNames w (FreeGroup.map Sum.inl v)) :
      PresGroup ρ) = _
    rw [SurfaceWordExpansion.foldNames_map_inl]

theorem inclusion_elimination (g : PresGroup (rel ρ w)) :
    inclusion ρ w (elimination ρ w g) = g := by
  have h : ((QuotientGroup.mk' (relSub (rel ρ w))).comp
      (FreeGroup.map (Sum.inl (β := I)))).comp (SurfaceWordExpansion.foldNames w) =
        QuotientGroup.mk' (relSub (rel ρ w)) := by
    apply FreeGroup.ext_hom
    rintro (a | i)
    · simp [SurfaceWordExpansion.foldNames]
    · simpa [SurfaceWordExpansion.foldNames] using (name_eq_word ρ w i).symm
  induction g using QuotientGroup.induction_on with
  | H v => exact DFunLike.congr_fun h v

def groupEquiv : PresGroup ρ ≃* PresGroup (rel ρ w) where
  toFun := inclusion ρ w
  invFun := elimination ρ w
  left_inv := elimination_inclusion ρ w
  right_inv := inclusion_elimination ρ w
  map_mul' := map_mul _

end FiniteChains.NamedPresentation
