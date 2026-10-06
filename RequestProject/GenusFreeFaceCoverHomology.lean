import RequestProject.PosetCoverFreeFaceHomology
import RequestProject.GenusCollapseStages

/-! The recorded genus-collapse pairs supply actual covered free-face retractions. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] {f : P → GenusTruncatedCell q}

/-- For every recorded pair, including cut-face pairs, deleting all lifts of
its free face preserves homology. No retraction or filling premise is assumed. -/
theorem genus_recorded_free_face_cover_homology (hf : IsPosetCover f)
    (left right : List (GenusCollapsePair q))
    (s : GenusTruncatedCell q) (t : QOld (cmpRel (GenusVertex q)))
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, truncatedFaceIndex s) :: right)) :
    AcyclicRelIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q left (f p) ∧ f p ≠ s) ∧
      ∀ n, ReflectsBoundsIn (fun p => genusCollapseStage q left (f p))
        (fun p => genusCollapseStage q left (f p) ∧ f p ≠ s) n := by
  let pair : GenusCollapsePair q := (qCubeToCoordinate t.1, truncatedFaceIndex s)
  have hpair : pair ∈ genusChainCollapse q := by
    rw [hsplit]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have hs : truncatedCellDimension s = 2 := genus_removedFace_dimension q s
    (List.mem_map.mpr ⟨pair, hpair, rfl⟩)
  have ht : t.1.spx.card = 3 := (genus_oldCell_removed_iff_dimension_three q t).mp
    (List.mem_map.mpr ⟨pair, hpair, rfl⟩)
  have htail : qCubeToCoordinate t.1 ∈ (pair :: right).map Prod.fst := by simp [pair]
  have hcert := genusCollapseStage_suffix_certificate q left (pair :: right) hsplit
  have hi : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q))
      (truncatedFaceIndex s) := by
    have hm : qCubeToCoordinate t.1 ∈
        spineInc (ASC.orderComplex (GenusVertex q)) (truncatedFaceIndex s) ∩
        Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left := by
      rw [hcert.2.1]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_inter.mp hm).1
  have htC : genusCollapseStage q left (Sum.inl t) :=
    ⟨genus_later_top_boundary_avoids_prefix_faces q left (pair :: right) hsplit
      (Sum.inl t) t htail (le_refl _),
      ((Collapse.mem_remainingTops _ _ _).mp hcert.1).2⟩
  have hne : (Sum.inl t : GenusTruncatedCell q) ≠ s := by
    intro he
    have hd := congrArg truncatedCellDimension he
    change t.1.spx.card = truncatedCellDimension s at hd
    omega
  apply cover_freeFace_homology hf htC (truncatedCell_le_of_inc s t hi) hne
  intro x hx hsx hxs
  have hdim : truncatedCellDimension x = 3 := by
    have hlt := truncatedCellDimension_strictMono (lt_of_le_of_ne hsx hxs.symm)
    have hmax := genusTruncatedCell_dimension_le_three q x
    omega
  cases x with
  | inr σ =>
      have hmax := genus_cutCell_dimension_le_two q σ
      omega
  | inl d =>
      have hd : d.1.spx.card = 3 := hdim
      have hinc := truncatedCell_inc_of_le s d hsx hs hd
        (genus_simplex_mem_faces q d.1.isSimplex)
      have hm := Finset.mem_inter.mpr ⟨hinc, genusCollapseStage_active_top q left d hx hd⟩
      rw [hcert.2.1] at hm
      have he : qCubeToCoordinate d.1 = qCubeToCoordinate t.1 := Finset.mem_singleton.mp hm
      exact congrArg Sum.inl (Subtype.ext (qCubeCoordinateEquiv.injective (Subtype.ext he)))

end FiniteChains.Davis.Genus
