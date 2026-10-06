module

public import RequestProject.GenusOrdinaryPairCollapse
public import RequestProject.PositiveBoundaryCoordinates

@[expose] public section

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem genusCollapseStage_cut_step_iff (left : List (GenusCollapsePair q))
    (t : QOld (cmpRel (GenusVertex q))) (hne : t.1.spx.Nonempty)
    (c : GenusTruncatedCell q) :
    genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, Sum.inr t.1.spx)]) c ↔
      (genusCollapseStage q left c ∧ c ≠ Sum.inr (fullCutCell t hne)) ∧ c ≠ Sum.inl t := by
  have hinj : Function.Injective
      (fun d : QOld (cmpRel (GenusVertex q)) => qCubeToCoordinate d.1) := by
    intro d e h
    exact Subtype.ext (qCubeCoordinateEquiv.injective (Subtype.ext h))
  cases c with
  | inl d =>
    simp only [genusCollapseStage, truncatedFaceIndex, List.map_append, List.map_cons,
      List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      ne_eq, Sum.inl.injEq, Sum.inl_ne_inr, hinj.eq_iff]
    tauto
  | inr σ =>
    have he : σ.1 = t.1.spx ↔ σ = fullCutCell t hne :=
      ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    simp [genusCollapseStage, truncatedFaceIndex, he]

theorem genus_cut_pair_stage_injIn
    (left right : List (GenusCollapsePair q))
    (t : QOld (cmpRel (GenusVertex q)))
    (hne : t.1.spx.Nonempty) (ht : t.1.spx.card = 3) (hpositive : t.1.sgn = 0)
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inr t.1.spx) :: right)) :
    InjIn (genusCollapseStage q left)
      (genusCollapseStage q
        (left ++ [(qCubeToCoordinate t.1, Sum.inr t.1.spx)])) := by
  let p : GenusCollapsePair q := (qCubeToCoordinate t.1, Sum.inr t.1.spx)
  have htail : qCubeToCoordinate t.1 ∈ (p :: right).map Prod.fst := by simp [p]
  have hc := genusCollapseStage_suffix_certificate q left (p :: right) hsplit
  have hfree := hc.2.1
  have hi : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q))
      (Sum.inr t.1.spx) := by
    have hm : qCubeToCoordinate t.1 ∈
        spineInc (ASC.orderComplex (GenusVertex q)) (Sum.inr t.1.spx) ∩
          Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left := by
      rw [hfree]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_inter.mp hm).1
  have htC : genusCollapseStage q left (Sum.inl t) :=
    ⟨genus_later_top_boundary_avoids_prefix_faces q left (p :: right) hsplit
        (Sum.inl t) t htail (le_refl _),
      ((Collapse.mem_remainingTops _ _ _).mp hc.1).2⟩
  have hf : truncatedCellDimension (Sum.inr (fullCutCell t hne) : GenusTruncatedCell q) = 2 := by
    change t.1.spx.card - 1 = 2
    omega
  have hface := genus_free_face_deletion_injIn q (genusCollapseStage q left)
    (Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left)
    (Sum.inr (fullCutCell t hne)) t hf ht htC
    (fun d hd hdim => genusCollapseStage_active_top q left d hd hdim) hfree
  have hJ (x : GenusTruncatedCell q) :
      x ≠ Sum.inr (fullCutCell t hne) ∧ x < Sum.inl t ↔
        (genusCollapseStage q left x ∧ x ≠ Sum.inr (fullCutCell t hne)) ∧ x < Sum.inl t := by
    constructor
    · rintro ⟨hne, hlt⟩
      exact ⟨⟨genusCollapseStage_boundary_mem q left (p :: right) hsplit t htail x hlt, hne⟩, hlt⟩
    · exact fun h => ⟨h.1.2, h.2⟩
  have htop : InjIn (fun x => genusCollapseStage q left x ∧ x ≠ Sum.inr (fullCutCell t hne))
      (fun x => (genusCollapseStage q left x ∧ x ≠ Sum.inr (fullCutCell t hne)) ∧ x ≠ Sum.inl t) := by
    apply injIn_delete_maximal
    · intro x _ htx
      exact genus_top_cell_maximal q t ht x htx
    · obtain ⟨x, hxf, hxt⟩ := genus_top_boundary_nonempty q (Sum.inr (fullCutCell t hne)) hf t ht
      exact ⟨x, (hJ x).mp ⟨hxf, hxt⟩⟩
    · exact connectedIn_congr hJ (positiveCutPuncturedBoundary_connectedIn t hne hpositive ht)
    · intro v l hv hp hl
      have hnull := positiveCutPuncturedBoundary_simplyConnectedIn t hne hpositive ht v l
        ((hJ v).mpr hv) hp (pathIn_mono (fun x hx => (hJ x).mpr hx) hl)
      exact hnull.mono (fun x hx => (hJ x).mp hx)
  have hpair := injIn_trans (fun _ h => h.1) hface htop
  intro v l hv hp hl hh
  have hnull := hpair v l
    ((genusCollapseStage_cut_step_iff q left t hne v).mp hv) hp
    (pathIn_mono (fun x hx => (genusCollapseStage_cut_step_iff q left t hne x).mp hx) hl) hh
  exact hnull.mono (fun x hx => (genusCollapseStage_cut_step_iff q left t hne x).mpr hx)


/-- Every recorded cut-face pair satisfies the local collapse comparison. -/
theorem genus_recorded_cut_pair_stage_injIn
    (left right : List (GenusCollapsePair q))
    (σ : CutCell (cmpRel (GenusVertex q))) (t : QOld (cmpRel (GenusVertex q)))
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inr σ.1) :: right)) :
    InjIn (genusCollapseStage q left)
      (genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, Sum.inr σ.1)])) := by
  classical
  have hp : (qCubeToCoordinate t.1, Sum.inr σ.1) ∈ genusChainCollapse q := by
    rw [hsplit]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have ht : t.1.spx.card = 3 := (genus_oldCell_removed_iff_dimension_three q t).mp
    (List.mem_map.mpr ⟨(qCubeToCoordinate t.1, Sum.inr σ.1), hp, rfl⟩)
  have hc := genusCollapseStage_suffix_certificate q left
    ((qCubeToCoordinate t.1, Sum.inr σ.1) :: right) hsplit
  have hi : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q))
      (Sum.inr σ.1) := by
    have hm : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q))
        (Sum.inr σ.1) ∩
        Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left := by
      rw [hc.2.1]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_inter.mp hm).1
  have he : qCubeToCoordinate t.1 = posCube σ.1 := by
    simp only [spineInc] at hi
    split at hi
    · exact Finset.mem_singleton.mp hi
    · simp at hi
  have hs : t.1.spx = σ.1 := by
    have hh := congrArg freeSet he
    simpa using hh
  have hpositive : t.1.sgn = 0 := by
    funext v
    have hh := qCubeToCoordinate_parity t.1 v
    rw [he] at hh
    by_cases hv : v ∈ σ.1
    · simpa [posCube, hv] using hh.symm
    · simpa [posCube, hv] using hh.symm
  have hne : t.1.spx.Nonempty := hs.symm ▸ σ.2.1
  have hstep := genus_cut_pair_stage_injIn q left right t hne ht hpositive
    (by simpa only [hs] using hsplit)
  simpa only [hs] using hstep

end FiniteChains.Davis.Genus
