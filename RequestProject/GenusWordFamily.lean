module

public import RequestProject.GenusWordInjection
public import RequestProject.BlockFamilyAmalgamation

@[expose] public section

/-! Simultaneous replacement by finite genus blocks, with independently varying genus. -/

namespace FiniteChains.Davis.Genus

open RACG Mirror Comb PresModel BlockFamily

variable {α Jr Sx : Type} (ρ : Jr ⊕ Sx → FreeGroup α)
  (q : Sx → ℕ) [∀ s, NeZero (q s)]
  (u : ∀ s, Fin (q s) × Bool → FreeGroup α)
  (T : ∀ s, SpanningTree
    (orderCx (QOld (cmpRel (SCell (gvc (q s)) (gec (q s)) (gc (q s)))))))

noncomputable def familyWordBlock (s : Sx) := wordBlock (q s) (u s) (T s) PUnit.unit

variable (hrho : ∀ s, ρ (Sum.inr s) = commWord (u s) (finitePairs (q s)))

include hrho in
/-- Each prescribed surface word is a consequence of its own finite block relators. -/
theorem familyWordBlock_consequence (s : Sx) :
    FreeGroup.map (Sum.inl (β := spineGens (T s))) (ρ (Sum.inr s)) ∈
      Subgroup.normalClosure (Set.range (familyWordBlock q u T s)) := by
  let φ := blockSubst (Zt := fun _ : PUnit.{1} => spineGens (T s))
    (fun _ => u s) PUnit.unit
  have hf := mem_relSub_spineBeta_commWord (T s) (gBase (q s)) (finiteSig (q s))
    (fun x => isPath_gSig (q s) (x.1.val, x.2)) (finitePairs (q s)) (finite_hfilling (q s))
  have hv : φ (commWord (fun x => FreeGroup.of (Sum.inl x)) (finitePairs (q s))) =
      FreeGroup.map (Sum.inl (β := spineGens (T s))) (ρ (Sum.inr s)) := by
    rw [map_commWord]
    simp only [φ, blockSubst_of_inl]
    rw [← map_commWord, hrho s]
  rw [← hv]
  apply map_mem_normalClosure φ ?_ hf
  rintro w ⟨m, rfl⟩
  exact Subgroup.subset_normalClosure ⟨m, rfl⟩

include hrho in
theorem familyWordBlock_filledF : FilledF ρ (familyWordBlock q u T) :=
  filledF_of_block_consequences ρ (familyWordBlock q u T)
    (familyWordBlock_consequence ρ q u T hrho)

/-- Actual simultaneous structural injectivity, for arbitrary families of prescribed words
and finite genus blocks. The genus and spanning tree may vary with the replaced entry. -/
theorem injective_substHomF_genus_word_family : Function.Injective
    (substHomF ρ (familyWordBlock q u T) (familyWordBlock_filledF ρ q u T hrho)) := by
  apply injective_substHomF_of_individual ρ (familyWordBlock q u T)
    (familyWordBlock_filledF ρ q u T hrho)
    (fun s => wordBlock_filledF (oneRel ρ s) (q s) (u s) (T s) (hrho s))
  intro s
  exact injective_substHomF_genus_words (oneRel ρ s) (q s) (u s) (T s) (hrho s)

/-- A spanning tree chosen from the proved connectedness of the concrete block. -/
noncomputable def chosenTree (n : ℕ) [NeZero n] : SpanningTree
    (orderCx (QOld (cmpRel (SCell (gvc n) (gec n) (gc n))))) :=
  Classical.choose (exists_spanningTree_genus n)

/-- The family has finitely many internal generators when the replaced-entry set is finite. -/
theorem finite_family_generators [Finite Sx] :
    Finite (Σ s, spineGens (T s)) := inferInstance

/-- The family has finitely many block relators when the replaced-entry set is finite. -/
theorem finite_family_relators [Finite Sx] :
    Finite (Σ s, spineRels
      (A := cmpRel (SCell (gvc (q s)) (gec (q s)) (gc (q s)))) (Fin (q s) × Bool)) :=
  inferInstance

/-- Simultaneous structural injectivity with all spanning trees constructed internally. -/
theorem injective_substHomF_genus_word_family_chosen : Function.Injective
    (substHomF ρ (familyWordBlock q u (fun s => chosenTree (q s)))
      (familyWordBlock_filledF ρ q u (fun s => chosenTree (q s)) hrho)) :=
  injective_substHomF_genus_word_family ρ q u (fun s => chosenTree (q s)) hrho

end FiniteChains.Davis.Genus
