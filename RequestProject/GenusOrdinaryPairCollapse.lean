module

public import RequestProject.GenusFreeFaceRetraction
public import RequestProject.OrdinaryTruncatedBoundary
public import RequestProject.GenusCollapseStages

@[expose] public section

/-! A complete elementary collapse comparison for an ordinary genus-block cube. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem genus_initial_ordinary_pair_collapse_injIn
    (f t : QOld (cmpRel (GenusVertex q)))
    (hf : f.1.spx.card = 2) (ht : t.1.spx.card = 3) (hordinary : t.1.sgn ≠ 0)
    (hfree : Collapse.IsFree (spineInc (ASC.orderComplex (GenusVertex q)))
      (topCubes (ASC.orderComplex (GenusVertex q)))
      (Sum.inl (qCubeToCoordinate f.1)) (qCubeToCoordinate t.1)) :
    InjIn (fun _ : GenusTruncatedCell q => True)
      (fun x => x ≠ Sum.inl f ∧ x ≠ Sum.inl t) := by
  have hi : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q))
      (Sum.inl (qCubeToCoordinate f.1)) := by
    have hm : qCubeToCoordinate t.1 ∈
        spineInc (ASC.orderComplex (GenusVertex q)) (Sum.inl (qCubeToCoordinate f.1)) ∩
          topCubes (ASC.orderComplex (GenusVertex q)) := by
      rw [hfree]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_inter.mp hm).1
  have hface := genus_initial_free_face_deletion_injIn q (Sum.inl f) t hf ht hfree
  have htop : InjIn (fun x : GenusTruncatedCell q => x ≠ Sum.inl f)
      (fun x => x ≠ Sum.inl f ∧ x ≠ Sum.inl t) := by
    apply injIn_delete_maximal
    · intro x _ htx
      exact genus_top_cell_maximal q t ht x htx
    · exact genus_top_boundary_nonempty q (Sum.inl f) hf t ht
    · exact ordinaryTruncatedBoundary_connectedIn hordinary hi
    · exact ordinaryTruncatedBoundary_simplyConnectedIn hordinary hi
  exact injIn_trans (fun _ h => h.1) hface htop

/-- An ordinary pair anywhere in the chosen collapse reflects null homotopies between
the actual consecutive stages. Earlier deletions impose no extra boundary hypothesis. -/
theorem genus_ordinary_pair_stage_injIn
    (left right : List (GenusCollapsePair q))
    (f t : QOld (cmpRel (GenusVertex q)))
    (hf : f.1.spx.card = 2) (ht : t.1.spx.card = 3) (hordinary : t.1.sgn ≠ 0)
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1)) :: right)) :
    InjIn (genusCollapseStage q left)
      (genusCollapseStage q
        (left ++ [(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1))])) := by
  let p : GenusCollapsePair q := (qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1))
  have htail : qCubeToCoordinate t.1 ∈ (p :: right).map Prod.fst := by simp [p]
  have hc := genusCollapseStage_suffix_certificate q left (p :: right) hsplit
  have hfree := hc.2.1
  have hi : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q))
      (Sum.inl (qCubeToCoordinate f.1)) := by
    have hm : qCubeToCoordinate t.1 ∈
        spineInc (ASC.orderComplex (GenusVertex q)) (Sum.inl (qCubeToCoordinate f.1)) ∩
          Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left := by
      rw [hfree]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_inter.mp hm).1
  have htC : genusCollapseStage q left (Sum.inl t) :=
    ⟨genus_later_top_boundary_avoids_prefix_faces q left (p :: right) hsplit
        (Sum.inl t) t htail (le_refl _),
      ((Collapse.mem_remainingTops _ _ _).mp hc.1).2⟩
  have hface := genus_free_face_deletion_injIn q (genusCollapseStage q left)
    (Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left)
    (Sum.inl f) t hf ht htC
    (fun d hd hdim => genusCollapseStage_active_top q left d hd hdim) hfree
  have hJ (x : GenusTruncatedCell q) :
      x ≠ Sum.inl f ∧ x < Sum.inl t ↔
        (genusCollapseStage q left x ∧ x ≠ Sum.inl f) ∧ x < Sum.inl t := by
    constructor
    · rintro ⟨hne, hlt⟩
      exact ⟨⟨genusCollapseStage_boundary_mem q left (p :: right) hsplit t htail x hlt, hne⟩, hlt⟩
    · exact fun h => ⟨h.1.2, h.2⟩
  have htop : InjIn (fun x => genusCollapseStage q left x ∧ x ≠ Sum.inl f)
      (fun x => (genusCollapseStage q left x ∧ x ≠ Sum.inl f) ∧ x ≠ Sum.inl t) := by
    apply injIn_delete_maximal
    · intro x _ htx
      exact genus_top_cell_maximal q t ht x htx
    · obtain ⟨x, hxf, hxt⟩ := genus_top_boundary_nonempty q (Sum.inl f) hf t ht
      exact ⟨x, (hJ x).mp ⟨hxf, hxt⟩⟩
    · exact connectedIn_congr hJ (ordinaryTruncatedBoundary_connectedIn hordinary hi)
    · intro v l hv hp hl
      have hnull := ordinaryTruncatedBoundary_simplyConnectedIn hordinary hi v l
        ((hJ v).mpr hv) hp (pathIn_mono (fun x hx => (hJ x).mpr hx) hl)
      exact hnull.mono (fun x hx => (hJ x).mp hx)
  have hpair := injIn_trans (fun _ h => h.1) hface htop
  intro v l hv hp hl hh
  have hnull := hpair v l
    ((genusCollapseStage_ordinary_step_iff q left f t v).mp hv) hp
    (pathIn_mono (fun x hx => (genusCollapseStage_ordinary_step_iff q left f t x).mp hx) hl) hh
  exact hnull.mono (fun x hx => (genusCollapseStage_ordinary_step_iff q left f t x).mpr hx)

/-- Every old-face pair in the chosen collapse satisfies the ordinary comparison, with
dimension and nonpositive-corner conditions derived from the actual recorded pair. -/
theorem genus_old_pair_stage_injIn
    (left right : List (GenusCollapsePair q))
    (f t : QOld (cmpRel (GenusVertex q)))
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1)) :: right)) :
    InjIn (genusCollapseStage q left)
      (genusCollapseStage q
        (left ++ [(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1))])) := by
  have hp : (qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1)) ∈ genusChainCollapse q := by
    rw [hsplit]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have hf : f.1.spx.card = 2 := genus_removedFace_dimension q (Sum.inl f)
    (List.mem_map.mpr ⟨(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1)), hp, rfl⟩)
  have ht : t.1.spx.card = 3 := (genus_oldCell_removed_iff_dimension_three q t).mp
    (List.mem_map.mpr ⟨(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1)), hp, rfl⟩)
  have hordinary : t.1.sgn ≠ 0 := by
    intro hs
    apply genusChainCollapse_old_face_nonpositive q (qCubeToCoordinate t.1)
      (qCubeToCoordinate f.1) hp
    simpa only [freeSet_qCubeToCoordinate] using qCubeToCoordinate_sgn_zero t.1 hs
  exact genus_ordinary_pair_stage_injIn q left right f t hf ht hordinary hsplit

end FiniteChains.Davis.Genus
