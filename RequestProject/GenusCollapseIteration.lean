import RequestProject.GenusCutPairCollapse
import RequestProject.GenusSpineTruncation

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

/-- Every admissible coordinate cube of positive dimension is an actual retained cell. -/
theorem exists_oldCell_of_coordinate (c : Cube (GenusVertex q))
    (hc : freeSet c ∈ (ASC.orderComplex (GenusVertex q)).faces)
    (hne : (freeSet c).Nonempty) :
    ∃ d : QOld (cmpRel (GenusVertex q)), qCubeToCoordinate d.1 = c := by
  have hs : IsSimplex (cmpRel (GenusVertex q)) (freeSet c) := by
    apply isSimplex_cmpRel_iff.mpr
    intro a ha b hb
    by_cases hab : a = b
    · subst b
      exact Or.inl (le_refl _)
    · exact hc ha hb hab
  let d := coordinateToQCube ⟨c, hs⟩
  have hd : qCubeToCoordinate d = c := coordinateToQCube_toCoordinate _
  have hold : ¬ (d.spx = ∅ ∧ d.sgn = 0) := by
    rintro ⟨he, _⟩
    exact Finset.nonempty_iff_ne_empty.mp hne he
  exact ⟨⟨d, hold⟩, hd⟩

/-- Every coordinate pair in the certificate decodes to a genuine top and facet. -/
theorem genus_pair_cells (p : GenusCollapsePair q)
    (hp : p ∈ genusChainCollapse q) :
    ∃ (t : QOld (cmpRel (GenusVertex q))) (f : GenusTruncatedCell q),
      qCubeToCoordinate t.1 = p.1 ∧ truncatedFaceIndex f = p.2 := by
  classical
  have hc := genusChainCollapse_isPairCollapse q
  have ht := mem_topCubes.mp (hc.top_mem hp)
  obtain ⟨t, htc⟩ := exists_oldCell_of_coordinate q p.1 ht.1
    (Finset.card_pos.mp (by have hh := ht.2; omega))
  have hi := hc.pair_inc hp
  cases hf : p.2 with
  | inl g =>
    rw [hf] at hi
    simp only [spineInc] at hi
    split at hi
    next hg =>
      obtain ⟨j, _, hjL, _⟩ := mem_cofaces.mp hi
      have hgL : freeSet g ∈ (ASC.orderComplex (GenusVertex q)).faces := by
        intro a ha b hb hab
        exact hjL (Finset.mem_insert_of_mem ha) (Finset.mem_insert_of_mem hb) hab
      obtain ⟨f, hfc⟩ := exists_oldCell_of_coordinate q g hgL
        (Finset.card_pos.mp (by omega))
      exact ⟨t, Sum.inl f, htc, by simp only [truncatedFaceIndex, hfc]⟩
    next => simp at hi
  | inr σ =>
    rw [hf] at hi
    simp only [spineInc] at hi
    split at hi
    next hσ =>
      have hs : IsSimplex (cmpRel (GenusVertex q)) σ := by
        apply isSimplex_cmpRel_iff.mpr
        intro a ha b hb
        by_cases hab : a = b
        · subst b
          exact Or.inl (le_refl _)
        · exact hσ.1 ha hb hab
      let f : CutCell (cmpRel (GenusVertex q)) :=
        ⟨σ, Finset.card_pos.mp (by have hh := hσ.2; omega), hs⟩
      exact ⟨t, Sum.inr f, htc, rfl⟩
    next => simp at hi

/-- Each pair in the chosen coordinate list reflects null homotopies at its stage. -/
theorem genus_pair_stage_injIn (left right : List (GenusCollapsePair q))
    (p : GenusCollapsePair q)
    (hsplit : genusChainCollapse q = left ++ p :: right) :
    InjIn (genusCollapseStage q left) (genusCollapseStage q (left ++ [p])) := by
  have hp : p ∈ genusChainCollapse q := by
    rw [hsplit]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  obtain ⟨t, f, ht, hf⟩ := genus_pair_cells q p hp
  have he : p = (qCubeToCoordinate t.1, truncatedFaceIndex f) :=
    Prod.ext ht.symm hf.symm
  rw [he] at hsplit ⊢
  cases f with
  | inl f => exact genus_old_pair_stage_injIn q left right f t hsplit
  | inr σ => exact genus_recorded_cut_pair_stage_injIn q left right σ t hsplit

theorem genusCollapseStage_append_subset (left right : List (GenusCollapsePair q))
    (c : GenusTruncatedCell q) (hc : genusCollapseStage q (left ++ right) c) :
    genusCollapseStage q left c := by
  constructor
  · intro hm
    exact hc.1 (by simpa only [List.map_append, List.mem_append] using Or.inl hm)
  · cases c with
    | inl d =>
      intro hm
      exact hc.2 (by simpa only [List.map_append, List.mem_append] using Or.inl hm)
    | inr σ => trivial

/-- Null homotopy reflection through the entire genuine geometric collapse. -/
theorem genus_collapse_suffix_injIn (right left : List (GenusCollapsePair q))
    (hsplit : genusChainCollapse q = left ++ right) :
    InjIn (genusCollapseStage q left) (genusCollapseStage q (left ++ right)) := by
  induction right generalizing left with
  | nil => simpa using injIn_self (genusCollapseStage q left)
  | cons p right ih =>
    have hfirst := genus_pair_stage_injIn q left right p hsplit
    have htail := ih (left ++ [p]) (by simpa only [List.append_assoc,
      List.singleton_append] using hsplit)
    have hcombined := injIn_trans
      (genusCollapseStage_append_subset q (left ++ [p]) right) hfirst htail
    simpa only [List.append_assoc, List.singleton_append] using hcombined

/-- The actual surviving spine reflects all based null homotopies of the truncated block. -/
theorem genusSpine_injIn :
    InjIn (fun _ : GenusTruncatedCell q => True)
      (fun c => c ∈ genusSpineCellSet q) := by
  have h := genus_collapse_suffix_injIn q (genusChainCollapse q) [] (by simp)
  intro v l hv hp hl hh
  have hnull := h v l
    (by simpa only [List.nil_append, genusCollapseStage_final_iff] using hv) hp
    (pathIn_mono (fun c hc => (genusCollapseStage_final_iff q c).mpr hc) hl)
    (hh.mono (fun c _ => genusCollapseStage_nil q c))
  exact hnull.mono (fun c hc => (genusCollapseStage_final_iff q c).mp hc)

theorem genusSpineToTruncated_pi1_injective :
    Function.Injective (pi1Map (genusSpineToTruncated q) (spineBase q)) := by
  have hincl : Function.Injective
      (pi1Map (orderCxMap (fun c : GenusSpineCell q => c.1) monotone_subtypeVal)
        (spineBase q)) :=
    pi1Map_injective_of_injIn (genusSpine_injIn q) monotone_subtypeVal
      (fun c => c.2) monotone_id (fun _ => rfl) (spineBase q)
  have hfactor (z : Pi1 (genusSpineCx q) (spineBase q)) :
      pi1Map (genusSpineToTruncated q) (spineBase q) z =
        pi1Map (orderCxMap (fun c : GenusSpineCell q => c.1) monotone_subtypeVal)
          (spineBase q) (strictOrderPi1Equiv (P := GenusSpineCell q) (spineBase q) z) := by
    induction z using Quotient.inductionOn with
    | h p =>
      apply congrArg Pi1.mk
      apply Subtype.ext
      simp [genusSpineToTruncated, mapPath, Hom.comp, List.map_map, Function.comp_def]
  intro z w he
  apply (strictOrderPi1Equiv (P := GenusSpineCell q) (spineBase q)).injective
  apply hincl
  rwa [← hfactor z, ← hfactor w]

theorem genusSpineToOld_pi1_injective :
    Function.Injective (pi1Map (genusSpineToOld q) (spineBase q)) :=
  (genusSpine_pi1_injective_iff q).mpr (genusSpineToTruncated_pi1_injective q)

end FiniteChains.Davis.Genus
