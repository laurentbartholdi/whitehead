import RequestProject.GenusCollapseIteration
import RequestProject.OrderComplexMaximalPath

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem genus_free_face_loop_representative
    (C : GenusTruncatedCell q → Prop) (S : Finset (Cube (GenusVertex q)))
    (f : GenusTruncatedCell q) (t : QOld (cmpRel (GenusVertex q)))
    (hf : truncatedCellDimension f = 2) (ht : t.1.spx.card = 3)
    (htC : C (Sum.inl t))
    (hactive : ∀ d : QOld (cmpRel (GenusVertex q)), C (Sum.inl d) →
      d.1.spx.card = 3 → qCubeToCoordinate d.1 ∈ S)
    (hfree : Collapse.IsFree (spineInc (ASC.orderComplex (GenusVertex q))) S
      (truncatedFaceIndex f) (qCubeToCoordinate t.1))
    (a : GenusTruncatedCell q) (p : List ((orderCx (GenusTruncatedCell q)).E × Bool))
    (ha : C a ∧ a ≠ f)
    (hp : IsPath (orderCx (GenusTruncatedCell q)).src (orderCx (GenusTruncatedCell q)).tgt p a a)
    (hC : PathIn C p) :
    ∃ l, IsPath (orderCx (GenusTruncatedCell q)).src (orderCx (GenusTruncatedCell q)).tgt l a a ∧
      PathIn (fun x => C x ∧ x ≠ f) l ∧ Htpy (orderCx (GenusTruncatedCell q)) a a p l := by
  have hinc : qCubeToCoordinate t.1 ∈
      spineInc (ASC.orderComplex (GenusVertex q)) (truncatedFaceIndex f) := by
    have hm : qCubeToCoordinate t.1 ∈
        spineInc (ASC.orderComplex (GenusVertex q)) (truncatedFaceIndex f) ∩ S := by
      rw [hfree]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_inter.mp hm).1
  have hft := truncatedCell_le_of_inc f t hinc
  have hne : (Sum.inl t : GenusTruncatedCell q) ≠ f := by
    intro he
    have hh := congrArg truncatedCellDimension he
    change t.1.spx.card = truncatedCellDimension f at hh
    omega
  apply loop_representative_delete_free_face htC hft hne ?_ ha hp hC
  intro x hx hfx hxf
  have hdim : truncatedCellDimension x = 3 := by
    have hlt := truncatedCellDimension_strictMono (lt_of_le_of_ne hfx hxf.symm)
    have hmax := genusTruncatedCell_dimension_le_three q x
    omega
  cases x with
  | inr σ =>
    have hh := genus_cutCell_dimension_le_two q σ
    omega
  | inl d =>
    have hd : d.1.spx.card = 3 := hdim
    have hL : d.1.spx ∈ (ASC.orderComplex (GenusVertex q)).faces := by
      intro a ha b hb _
      exact (isSimplex_cmpRel_iff.mp d.1.isSimplex) a ha b hb
    have hi := truncatedCell_inc_of_le f d hfx hf hd hL
    have hm := Finset.mem_inter.mpr ⟨hi, hactive d hx hd⟩
    rw [hfree] at hm
    have he : qCubeToCoordinate d.1 = qCubeToCoordinate t.1 :=
      Finset.mem_singleton.mp hm
    have hc : d.1 = t.1 := qCubeCoordinateEquiv.injective (Subtype.ext he)
    exact congrArg Sum.inl (Subtype.ext hc)


theorem genus_ordinary_pair_loop_representative
    (left right : List (GenusCollapsePair q))
    (f t : QOld (cmpRel (GenusVertex q)))
    (hf : f.1.spx.card = 2) (ht : t.1.spx.card = 3) (hordinary : t.1.sgn ≠ 0)
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1)) :: right))
    (a : GenusTruncatedCell q) (loop : List ((orderCx (GenusTruncatedCell q)).E × Bool))
    (ha : genusCollapseStage q
      (left ++ [(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1))]) a)
    (hpath : IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt loop a a)
    (hC : PathIn (genusCollapseStage q left) loop) :
    ∃ l, IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt l a a ∧
      PathIn (genusCollapseStage q
        (left ++ [(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1))])) l ∧
      Htpy (orderCx (GenusTruncatedCell q)) a a loop l := by
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
  have ha' := (genusCollapseStage_ordinary_step_iff q left f t a).mp ha
  obtain ⟨l, hl, hlf, hhl⟩ := genus_free_face_loop_representative q (genusCollapseStage q left)
    (Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left)
    (Sum.inl f) t hf ht htC
    (fun d hd hdim => genusCollapseStage_active_top q left d hd hdim) hfree a loop ha'.1 hpath hC
  have hJ (x : GenusTruncatedCell q) :
      x ≠ Sum.inl f ∧ x < Sum.inl t ↔
        (genusCollapseStage q left x ∧ x ≠ Sum.inl f) ∧ x < Sum.inl t := by
    constructor
    · rintro ⟨hne, hlt⟩
      exact ⟨⟨genusCollapseStage_boundary_mem q left (p :: right) hsplit t htail x hlt, hne⟩, hlt⟩
    · exact fun h => ⟨h.1.2, h.2⟩
  have hconn := connectedIn_congr hJ (ordinaryTruncatedBoundary_connectedIn hordinary hi)
  obtain ⟨r, hr, hrB, hhr⟩ := maximal_path_representative
    (C := fun x => genusCollapseStage q left x ∧ x ≠ Sum.inl f)
    (t := Sum.inl t) (fun x _ htx => genus_top_cell_maximal q t ht x htx)
    hconn l ha' ha' hl hlf
  exact ⟨r, hr, pathIn_mono
    (fun x hx => (genusCollapseStage_ordinary_step_iff q left f t x).mpr hx) hrB,
    hhl.trans hhr⟩

theorem genus_cut_pair_loop_representative
    (left right : List (GenusCollapsePair q))
    (t : QOld (cmpRel (GenusVertex q)))
    (hne : t.1.spx.Nonempty) (ht : t.1.spx.card = 3) (hpositive : t.1.sgn = 0)
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inr t.1.spx) :: right))
    (a : GenusTruncatedCell q) (loop : List ((orderCx (GenusTruncatedCell q)).E × Bool))
    (ha : genusCollapseStage q
      (left ++ [(qCubeToCoordinate t.1, Sum.inr t.1.spx)]) a)
    (hpath : IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt loop a a)
    (hC : PathIn (genusCollapseStage q left) loop) :
    ∃ l, IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt l a a ∧
      PathIn (genusCollapseStage q
        (left ++ [(qCubeToCoordinate t.1, Sum.inr t.1.spx)])) l ∧
      Htpy (orderCx (GenusTruncatedCell q)) a a loop l := by
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
  have ha' := (genusCollapseStage_cut_step_iff q left t hne a).mp ha
  obtain ⟨l, hl, hlf, hhl⟩ := genus_free_face_loop_representative q (genusCollapseStage q left)
    (Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left)
    (Sum.inr (fullCutCell t hne)) t hf ht htC
    (fun d hd hdim => genusCollapseStage_active_top q left d hd hdim) hfree a loop ha'.1 hpath hC
  have hJ (x : GenusTruncatedCell q) :
      x ≠ Sum.inr (fullCutCell t hne) ∧ x < Sum.inl t ↔
        (genusCollapseStage q left x ∧ x ≠ Sum.inr (fullCutCell t hne)) ∧ x < Sum.inl t := by
    constructor
    · rintro ⟨hne, hlt⟩
      exact ⟨⟨genusCollapseStage_boundary_mem q left (p :: right) hsplit t htail x hlt, hne⟩, hlt⟩
    · exact fun h => ⟨h.1.2, h.2⟩
  have hconn := connectedIn_congr hJ (positiveCutPuncturedBoundary_connectedIn t hne hpositive ht)
  obtain ⟨r, hr, hrB, hhr⟩ := maximal_path_representative
    (C := fun x => genusCollapseStage q left x ∧ x ≠ Sum.inr (fullCutCell t hne))
    (t := Sum.inl t) (fun x _ htx => genus_top_cell_maximal q t ht x htx)
    hconn l ha' ha' hl hlf
  exact ⟨r, hr, pathIn_mono
    (fun x hx => (genusCollapseStage_cut_step_iff q left t hne x).mpr hx) hrB,
    hhl.trans hhr⟩

theorem genus_old_pair_loop_representative
    (left right : List (GenusCollapsePair q))
    (f t : QOld (cmpRel (GenusVertex q)))
    (hsplit : genusChainCollapse q = left ++ ((qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1)) :: right))
    (a : GenusTruncatedCell q) (loop : List ((orderCx (GenusTruncatedCell q)).E × Bool))
    (ha : genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1))]) a)
    (hpath : IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt loop a a)
    (hC : PathIn (genusCollapseStage q left) loop) :
    ∃ l, IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt l a a ∧
      PathIn (genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1))])) l ∧
      Htpy (orderCx (GenusTruncatedCell q)) a a loop l := by
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
  exact genus_ordinary_pair_loop_representative q left right f t hf ht hordinary hsplit a loop ha hpath hC

theorem genus_recorded_cut_pair_loop_representative
    (left right : List (GenusCollapsePair q))
    (σ : CutCell (cmpRel (GenusVertex q))) (t : QOld (cmpRel (GenusVertex q)))
    (hsplit : genusChainCollapse q = left ++ ((qCubeToCoordinate t.1, Sum.inr σ.1) :: right))
    (a : GenusTruncatedCell q) (loop : List ((orderCx (GenusTruncatedCell q)).E × Bool))
    (ha : genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, Sum.inr σ.1)]) a)
    (hpath : IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt loop a a)
    (hC : PathIn (genusCollapseStage q left) loop) :
    ∃ l, IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt l a a ∧
      PathIn (genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, Sum.inr σ.1)])) l ∧
      Htpy (orderCx (GenusTruncatedCell q)) a a loop l := by
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
  have hstep := genus_cut_pair_loop_representative q left right t hne ht hpositive
    (by simpa only [hs] using hsplit) a loop
    (by simpa only [hs] using ha) hpath hC
  simpa only [hs] using hstep

theorem genus_pair_loop_representative
    (left right : List (GenusCollapsePair q))
    (p : GenusCollapsePair q)
    (hsplit : genusChainCollapse q = left ++ (p :: right))
    (a : GenusTruncatedCell q) (loop : List ((orderCx (GenusTruncatedCell q)).E × Bool))
    (ha : genusCollapseStage q (left ++ [p]) a)
    (hpath : IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt loop a a)
    (hC : PathIn (genusCollapseStage q left) loop) :
    ∃ l, IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt l a a ∧
      PathIn (genusCollapseStage q (left ++ [p])) l ∧
      Htpy (orderCx (GenusTruncatedCell q)) a a loop l := by
  have hp : p ∈ genusChainCollapse q := by
    rw [hsplit]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  obtain ⟨t, f, ht, hf⟩ := genus_pair_cells q p hp
  have he : p = (qCubeToCoordinate t.1, truncatedFaceIndex f) := Prod.ext ht.symm hf.symm
  rw [he] at hsplit ha ⊢
  cases f with
  | inl f => exact genus_old_pair_loop_representative q left right f t hsplit a loop ha hpath hC
  | inr σ => exact genus_recorded_cut_pair_loop_representative q left right σ t hsplit a loop ha hpath hC

/-- Construct a loop in the terminal stage of any actual suffix of the chosen collapse. -/
theorem genus_collapse_suffix_loop_representative
    (right left : List (GenusCollapsePair q))
    (hsplit : genusChainCollapse q = left ++ right)
    (a : GenusTruncatedCell q) (loop : List ((orderCx (GenusTruncatedCell q)).E × Bool))
    (ha : genusCollapseStage q (left ++ right) a)
    (hpath : IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt loop a a)
    (hC : PathIn (genusCollapseStage q left) loop) :
    ∃ l, IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt l a a ∧
      PathIn (genusCollapseStage q (left ++ right)) l ∧
      Htpy (orderCx (GenusTruncatedCell q)) a a loop l := by
  induction right generalizing left loop with
  | nil => exact ⟨loop, hpath, by simpa using hC, Htpy.refl _⟩
  | cons p right ih =>
    have haTail : genusCollapseStage q ((left ++ [p]) ++ right) a := by
      simpa only [List.append_assoc, List.singleton_append] using ha
    have haFirst := genusCollapseStage_append_subset q (left ++ [p]) right a haTail
    obtain ⟨l, hl, hlC, hhl⟩ := genus_pair_loop_representative q left right p hsplit
      a loop haFirst hpath hC
    obtain ⟨r, hr, hrC, hhr⟩ := ih (left ++ [p])
      (by simpa only [List.append_assoc, List.singleton_append] using hsplit)
      l haTail hl hlC
    exact ⟨r, hr, by simpa only [List.append_assoc, List.singleton_append] using hrC,
      hhl.trans hhr⟩

/-- Every loop of the truncated block based in its surviving spine is represented in that spine. -/
theorem genusSpine_loop_representative (a : GenusTruncatedCell q)
    (loop : List ((orderCx (GenusTruncatedCell q)).E × Bool))
    (ha : a ∈ genusSpineCellSet q)
    (hpath : IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt loop a a) :
    ∃ l, IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt l a a ∧
      PathIn (fun c => c ∈ genusSpineCellSet q) l ∧
      Htpy (orderCx (GenusTruncatedCell q)) a a loop l := by
  obtain ⟨l, hl, hC, hh⟩ := genus_collapse_suffix_loop_representative q
    (genusChainCollapse q) [] (by simp) a loop
    ((genusCollapseStage_final_iff q a).mpr ha) hpath
    (fun e _ => ⟨genusCollapseStage_nil q e.1.1.1, genusCollapseStage_nil q e.1.1.2⟩)
  exact ⟨l, hl, pathIn_mono (fun c hc => (genusCollapseStage_final_iff q c).mp hc) hC, hh⟩

theorem genusSpineToTruncated_pi1_factor_weak
    (z : Pi1 (genusSpineCx q) (spineBase q)) :
    pi1Map (genusSpineToTruncated q) (spineBase q) z =
      pi1Map (orderCxMap (fun c : GenusSpineCell q => c.1) monotone_subtypeVal)
        (spineBase q) (strictOrderPi1Equiv (P := GenusSpineCell q) (spineBase q) z) := by
  induction z using Quotient.inductionOn with
  | h p =>
    apply congrArg Pi1.mk
    apply Subtype.ext
    simp [genusSpineToTruncated, mapPath, Hom.comp, List.map_map, Function.comp_def]

theorem genusSpineToTruncated_pi1_surjective :
    Function.Surjective (pi1Map (genusSpineToTruncated q) (spineBase q)) := by
  rintro ⟨p⟩
  obtain ⟨r, hr, hrB, hh⟩ := genusSpine_loop_representative q
    (spineBase q).1 p.1 (spineBase q).2 p.2
  let lifted : Loop (orderCx (GenusSpineCell q)) (spineBase q) :=
    ⟨liftPathIn r hrB, isPath_liftPathIn r hrB (spineBase q).2 (spineBase q).2 hr⟩
  refine ⟨(strictOrderPi1Equiv (P := GenusSpineCell q) (spineBase q)).symm (Pi1.mk lifted), ?_⟩
  rw [genusSpineToTruncated_pi1_factor_weak, MulEquiv.apply_symm_apply]
  apply Quotient.sound
  change Htpy (orderCx (GenusTruncatedCell q)) (spineBase q).1 (spineBase q).1
    (mapPath (subposetHom (fun c => c ∈ genusSpineCellSet q)) (liftPathIn r hrB)) p.1
  rw [mapPath_liftPathIn]
  exact hh.symm

noncomputable def genusSpineToTruncatedPi1Equiv :
    Pi1 (genusSpineCx q) (spineBase q) ≃*
      Pi1 (orderCx (GenusTruncatedCell q)) ((genusSpineToTruncated q).onV (spineBase q)) :=
  MulEquiv.ofBijective (pi1Map (genusSpineToTruncated q) (spineBase q))
    ⟨genusSpineToTruncated_pi1_injective q, genusSpineToTruncated_pi1_surjective q⟩

theorem genusSpineToOld_pi1_surjective :
    Function.Surjective (pi1Map (genusSpineToOld q) (spineBase q)) := by
  intro z
  obtain ⟨v, hv⟩ := truncatedRetraction_pi1_surjective_at
    ((genusSpineToTruncated q).onV (spineBase q)) z
  obtain ⟨w, hw⟩ := genusSpineToTruncated_pi1_surjective q v
  exact ⟨w, by rw [genusSpine_pi1_factor, hw]; exact hv⟩

noncomputable def genusSpineToOldPi1Equiv :
    Pi1 (genusSpineCx q) (spineBase q) ≃*
      Pi1 (orderCx (QOld (cmpRel (GenusVertex q)))) ((genusSpineToOld q).onV (spineBase q)) :=
  MulEquiv.ofBijective (pi1Map (genusSpineToOld q) (spineBase q))
    ⟨genusSpineToOld_pi1_injective q, genusSpineToOld_pi1_surjective q⟩

end FiniteChains.Davis.Genus
