module

public import RequestProject.BlockSurfaceFilling

@[expose] public section

/-!
Naming arbitrary words in a surface relation. The named presentation retains the old
relators, adds one defining relation for each marked word, and replaces the surface word
by the same product of commutators in the new generators. Its group is isomorphic to the
original presentation group. No finiteness of the index sets is needed.
-/

namespace FiniteChains
namespace SurfaceWordExpansion

universe u

variable {α Jr I : Type u}
  (ρ : Jr ⊕ PUnit.{u + 1} → FreeGroup α) (w : I → FreeGroup α) (ps : List (I × I))

/-- The formal surface word in the newly named generators. -/
def formalSurface : FreeGroup (α ⊕ I) :=
  Davis.commWord (fun i => FreeGroup.of (Sum.inr i)) ps

/-- Retained relators, word definitions, and the formal surface relator. -/
def expandedRel : (Jr ⊕ I) ⊕ PUnit.{u + 1} → FreeGroup (α ⊕ I)
  | Sum.inl (Sum.inl j) => FreeGroup.map Sum.inl (ρ (Sum.inl j))
  | Sum.inl (Sum.inr i) => FreeGroup.of (Sum.inr i) * (FreeGroup.map Sum.inl (w i))⁻¹
  | Sum.inr _ => formalSurface (α := α) ps

/-- Eliminate each new name by substituting the word it names. -/
def foldNames : FreeGroup (α ⊕ I) →* FreeGroup α :=
  FreeGroup.lift (Sum.elim FreeGroup.of w)

 theorem foldNames_map_inl (v : FreeGroup α) :
    foldNames w (FreeGroup.map (Sum.inl (β := I)) v) = v := by
  have h : (foldNames w).comp (FreeGroup.map (Sum.inl (β := I))) = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro a
    simp [foldNames]
  exact DFunLike.congr_fun h v

 theorem foldNames_formalSurface :
    foldNames w (formalSurface (α := α) ps) = Davis.commWord w ps := by
  rw [formalSurface, Davis.map_commWord]
  apply Davis.commWord_congr
  intro i
  simp [foldNames]

/-- The defining relators identify each new name with the prescribed old word. -/
 theorem name_eq_word (i : I) :
    (QuotientGroup.mk (FreeGroup.of (Sum.inr i)) : PresGroup (expandedRel ρ w ps)) =
      QuotientGroup.mk (FreeGroup.map Sum.inl (w i)) := by
  have h : (QuotientGroup.mk
      (FreeGroup.of (Sum.inr i) * (FreeGroup.map Sum.inl (w i))⁻¹) :
        PresGroup (expandedRel ρ w ps)) = 1 :=
    (QuotientGroup.eq_one_iff _).2
      (Subgroup.subset_normalClosure ⟨Sum.inl (Sum.inr i), rfl⟩)
  change (QuotientGroup.mk' (relSub (expandedRel ρ w ps)))
    (FreeGroup.of (Sum.inr i) * (FreeGroup.map Sum.inl (w i))⁻¹) = 1 at h
  rw [map_mul, map_inv] at h
  exact mul_inv_eq_one.mp h

variable (hrho : ρ (Sum.inr PUnit.unit) = Davis.commWord w ps)

include hrho

 theorem old_relator_eq_one (j : Jr ⊕ PUnit.{u + 1}) :
    (QuotientGroup.mk (FreeGroup.map (Sum.inl (β := I)) (ρ j)) :
      PresGroup (expandedRel ρ w ps)) = 1 := by
  rcases j with j | s
  · exact (QuotientGroup.eq_one_iff _).2
      (Subgroup.subset_normalClosure ⟨Sum.inl (Sum.inl j), rfl⟩)
  · cases s
    rw [hrho]
    let q := QuotientGroup.mk' (relSub (expandedRel ρ w ps))
    change q (FreeGroup.map Sum.inl (Davis.commWord w ps)) = 1
    rw [Davis.map_commWord, Davis.map_commWord]
    have he : Davis.commWord (fun i => q (FreeGroup.map Sum.inl (w i))) ps =
        q (formalSurface (α := α) ps) := by
      rw [formalSurface, Davis.map_commWord]
      exact Davis.commWord_congr (fun i => (name_eq_word ρ w ps i).symm) ps
    rw [he]
    exact (QuotientGroup.eq_one_iff _).2
      (Subgroup.subset_normalClosure ⟨Sum.inr PUnit.unit, rfl⟩)

/-- The old generators map into the named presentation group. -/
def inclusion : PresGroup ρ →* PresGroup (expandedRel ρ w ps) :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (relSub (expandedRel ρ w ps))).comp (FreeGroup.map Sum.inl))
    (by
      refine Subgroup.normalClosure_le_normal ?_
      rintro _ ⟨j, rfl⟩
      exact old_relator_eq_one ρ w ps hrho j)

 theorem folded_relator_eq_one (j : (Jr ⊕ I) ⊕ PUnit.{u + 1}) :
    (QuotientGroup.mk (foldNames w (expandedRel ρ w ps j)) : PresGroup ρ) = 1 := by
  rcases j with j | s
  · rcases j with j | i
    · change (QuotientGroup.mk (foldNames w (FreeGroup.map Sum.inl (ρ (Sum.inl j)))) :
        PresGroup ρ) = 1
      rw [foldNames_map_inl]
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure ⟨Sum.inl j, rfl⟩)
    · change (QuotientGroup.mk' (relSub ρ))
        (foldNames w (FreeGroup.of (Sum.inr i) * (FreeGroup.map Sum.inl (w i))⁻¹)) = 1
      rw [map_mul, map_inv, foldNames_map_inl]
      simp [foldNames]
  · cases s
    rw [show expandedRel ρ w ps (Sum.inr PUnit.unit) = formalSurface (α := α) ps from rfl,
      foldNames_formalSurface, ← hrho]
    exact (QuotientGroup.eq_one_iff _).2
      (Subgroup.subset_normalClosure ⟨Sum.inr PUnit.unit, rfl⟩)

/-- Word substitution induces the inverse map on presented groups. -/
def elimination : PresGroup (expandedRel ρ w ps) →* PresGroup ρ :=
  QuotientGroup.lift _ ((QuotientGroup.mk' (relSub ρ)).comp (foldNames w)) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    exact folded_relator_eq_one ρ w ps hrho j)

 theorem elimination_inclusion (g : PresGroup ρ) :
    elimination ρ w ps hrho (inclusion ρ w ps hrho g) = g := by
  induction g using QuotientGroup.induction_on with
  | H v =>
    change (QuotientGroup.mk (foldNames w (FreeGroup.map Sum.inl v)) : PresGroup ρ) = _
    rw [foldNames_map_inl]

 theorem inclusion_elimination (g : PresGroup (expandedRel ρ w ps)) :
    inclusion ρ w ps hrho (elimination ρ w ps hrho g) = g := by
  have h : ((QuotientGroup.mk' (relSub (expandedRel ρ w ps))).comp
      (FreeGroup.map (Sum.inl (β := I)))).comp (foldNames w) =
        QuotientGroup.mk' (relSub (expandedRel ρ w ps)) := by
    apply FreeGroup.ext_hom
    rintro (a | i)
    · simp [foldNames]
    · simpa [foldNames] using (name_eq_word ρ w ps i).symm
  induction g using QuotientGroup.induction_on with
  | H v => exact DFunLike.congr_fun h v

/-- Naming all the marked words preserves the original presentation group. -/
def groupEquiv : PresGroup ρ ≃* PresGroup (expandedRel ρ w ps) where
  toFun := inclusion ρ w ps hrho
  invFun := elimination ρ w ps hrho
  left_inv := elimination_inclusion ρ w ps hrho
  right_inv := inclusion_elimination ρ w ps hrho
  map_mul' := map_mul _

end SurfaceWordExpansion
end FiniteChains
