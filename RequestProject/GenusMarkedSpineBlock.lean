module

public import RequestProject.GenusNamedSpineComparison
public import RequestProject.BlockFamilyAmalgamation

@[expose] public section

/-! Genuine finite spine relators in the distinguished/internal order used by substitution. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

abbrev MarkedSpineGen := (Fin q × Bool) ⊕ SpinePresentationGen q

noncomputable def markedSpineBeta (m : NamedSpineRel q) : FreeGroup (MarkedSpineGen q) :=
  FreeGroup.map Sum.swap (namedSpinePresentation q m)

theorem freeGroup_map_swap_swap {α β : Type} (z : FreeGroup (α ⊕ β)) :
    FreeGroup.map Sum.swap (FreeGroup.map Sum.swap z) = z := by
  have h : (FreeGroup.map (Sum.swap : β ⊕ α → α ⊕ β)).comp
      (FreeGroup.map (Sum.swap : α ⊕ β → β ⊕ α)) = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    rintro (a | b) <;> simp
  exact DFunLike.congr_fun h z

noncomputable def markedSpineToOldHom :
    FreeGroup (MarkedSpineGen q) →*
      Pi1 (orderCx (QOld (cmpRel (GenusVertex q))))
        ((genusSpineToOld q).onV (spineBase q)) :=
  (namedSpineToOldEquiv q).toMonoidHom.comp
    ((QuotientGroup.mk' (relSub (namedSpinePresentation q))).comp (FreeGroup.map Sum.swap))

/-- All genuine marked block relators die under the constructed geometric block map. -/
theorem markedSpineToOldHom_rel (m : NamedSpineRel q) :
    markedSpineToOldHom q (markedSpineBeta q m) = 1 := by
  change (namedSpineToOldEquiv q).toMonoidHom
    (QuotientGroup.mk (FreeGroup.map Sum.swap
      (FreeGroup.map Sum.swap (namedSpinePresentation q m)))) = 1
  rw [freeGroup_map_swap_swap]
  have h : (QuotientGroup.mk (namedSpinePresentation q m) :
      PresGroup (namedSpinePresentation q)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨m, rfl⟩)
  rw [h, map_one]

/-- The distinguished generators have exactly the actual geometric marking. -/
theorem markedSpineToOldHom_mark (x : Fin q × Bool) :
    markedSpineToOldHom q (FreeGroup.of (Sum.inl x)) =
      pi1Map (genusSpineToOld q) (spineBase q) (Pi1.mk (spineMarkedLoop q x)) := by
  change namedSpineToOldEquiv q
    (QuotientGroup.mk (FreeGroup.map Sum.swap (FreeGroup.of (Sum.inl x)))) = _
  simp only [FreeGroup.map.of, Sum.swap_inl]
  exact namedSpineToOld_marked q x

/-- The surface word is a consequence of the actual reordered finite spine relators. -/
theorem markedSpine_surface_mem :
    commWord (fun x : Fin q × Bool => FreeGroup.of (Sum.inl x : MarkedSpineGen q))
      (finitePairs q) ∈ relSub (markedSpineBeta q) := by
  have h : commWord (fun x : Fin q × Bool =>
      FreeGroup.of (Sum.inr x : NamedSpineGen q)) (finitePairs q) ∈
      relSub (namedSpinePresentation q) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (relSub (namedSpinePresentation q)))
      (commWord (fun x => FreeGroup.of (Sum.inr x)) (finitePairs q)) = 1
    rw [map_commWord]
    exact namedSpine_surface_filling q
  have hm := map_mem_normalClosure (FreeGroup.map Sum.swap)
    (N := Set.range (markedSpineBeta q)) (fun z hz => by
      obtain ⟨m, rfl⟩ := hz
      exact Subgroup.subset_normalClosure ⟨m, rfl⟩) h
  simpa only [relSub, map_commWord, FreeGroup.map.of, Sum.swap_inr] using hm

/-- Simultaneous replacement by genuine finite spine relators fills each replaced word. -/
theorem markedSpine_filled {α Jr Sx : Type}
    (ρ : Jr ⊕ Sx → FreeGroup α) (u : Sx → Fin q × Bool → FreeGroup α)
    (hrho : ∀ s, ρ (Sum.inr s) = commWord (u s) (finitePairs q)) :
    BlockFamily.FilledF ρ (fun s m =>
      BlockFamily.blockSubst (Zt := fun _ => SpinePresentationGen q) u s
        (markedSpineBeta q m)) := by
  apply BlockFamily.filledF_of_block_consequences
  intro s
  have h := map_mem_normalClosure
    (BlockFamily.blockSubst (Zt := fun _ => SpinePresentationGen q) u s)
    (N := Set.range (fun m => BlockFamily.blockSubst
      (Zt := fun _ => SpinePresentationGen q) u s (markedSpineBeta q m)))
    (fun z hz => by
      obtain ⟨m, rfl⟩ := hz
      exact Subgroup.subset_normalClosure ⟨m, rfl⟩) (markedSpine_surface_mem q)
  rw [map_commWord] at h
  simp only [BlockFamily.blockSubst_of_inl] at h
  rw [hrho s, map_commWord]
  exact h

/-- The actual geometric block map supplies the relator checks for substitution.
Only the receiver inclusion and the reading of the prescribed words remain inputs. -/
theorem markedSpine_substitution_injective {α Jr Sx H : Type} [Group H]
    (ρ : Jr ⊕ Sx → FreeGroup α) (u : Sx → Fin q × Bool → FreeGroup α)
    (hrho : ∀ s, ρ (Sum.inr s) = commWord (u s) (finitePairs q))
    (j : PresGroup ρ →* H) (hj : Function.Injective j)
    (receiver : Sx → Pi1 (orderCx (QOld (cmpRel (GenusVertex q))))
      ((genusSpineToOld q).onV (spineBase q)) →* H)
    (hread : ∀ s x, receiver s
      (pi1Map (genusSpineToOld q) (spineBase q) (Pi1.mk (spineMarkedLoop q x))) =
        j (QuotientGroup.mk (u s x))) :
    Function.Injective (BlockFamily.substHomF ρ (fun s m =>
      BlockFamily.blockSubst (Zt := fun _ => SpinePresentationGen q) u s
        (markedSpineBeta q m)) (markedSpine_filled q ρ u hrho)) := by
  apply BlockFamily.injective_substHomF_of_markedBlock u
    (fun _ => markedSpineBeta q) (markedSpine_filled q ρ u hrho) j hj
    (fun s => (receiver s).comp (markedSpineToOldHom q))
  · intro s x
    rw [MonoidHom.comp_apply, markedSpineToOldHom_mark]
    exact hread s x
  · intro s m
    rw [MonoidHom.comp_apply, markedSpineToOldHom_rel, map_one]

end FiniteChains.Davis.Genus
