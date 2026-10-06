import RequestProject.GenusSpineCells
import RequestProject.TruncatedCellIncidence
import RequestProject.OrderComplexFreeFace

/-! Homotopy reflection for deletion of an actual free face at a genus collapse stage. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem genus_top_cell_maximal (t : QOld (cmpRel (GenusVertex q)))
    (ht : t.1.spx.card = 3) (x : GenusTruncatedCell q)
    (htx : (Sum.inl t : GenusTruncatedCell q) ≤ x) : x = Sum.inl t := by
  have hmax := genusTruncatedCell_dimension_le_three q x
  have hmono := truncatedCellDimension_monotone htx
  change t.1.spx.card ≤ truncatedCellDimension x at hmono
  have he : truncatedCellDimension (Sum.inl t : GenusTruncatedCell q) =
      truncatedCellDimension x := by
    change t.1.spx.card = truncatedCellDimension x
    omega
  exact (truncatedCell_eq_of_le_of_dimension_eq htx he).symm

/-- A top cube has a genuine old vertex on its boundary different from any deleted two-face.
Use the negative value on every free coordinate, so the removed positive vertex is avoided. -/
theorem genus_top_boundary_nonempty (f : GenusTruncatedCell q)
    (hf : truncatedCellDimension f = 2) (t : QOld (cmpRel (GenusVertex q)))
    (ht : t.1.spx.card = 3) :
    ∃ x : GenusTruncatedCell q, x ≠ f ∧ x < Sum.inl t := by
  classical
  let v : QCube (cmpRel (GenusVertex q)) := {
    spx := ∅
    sgn := fun j => if j ∈ t.1.spx then 1 else t.1.sgn j
    isSimplex := isSimplex_empty
    sgn_eq_zero := by simp }
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < t.1.spx.card)
  have hv : ¬ (v.spx = ∅ ∧ v.sgn = 0) := by
    rintro ⟨_, hs⟩
    have hh := congrFun hs j
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    change (if j ∈ t.1.spx then (1 : ZMod 2) else t.1.sgn j) = 0 at hh
    rw [if_pos hj] at hh
    exact h10 hh
  let w : QOld (cmpRel (GenusVertex q)) := ⟨v, hv⟩
  have hw : (Sum.inl w : GenusTruncatedCell q) ≤ Sum.inl t := by
    refine ⟨Finset.empty_subset _, ?_⟩
    intro k hk
    simp [w, v, hk]
  have hdim : truncatedCellDimension (Sum.inl w : GenusTruncatedCell q) = 0 := rfl
  refine ⟨Sum.inl w, ?_, lt_of_le_of_ne hw ?_⟩
  · intro he
    have hh := congrArg truncatedCellDimension he
    omega
  · intro he
    have hh := congrArg truncatedCellDimension he
    change truncatedCellDimension (Sum.inl w : GenusTruncatedCell q) = t.1.spx.card at hh
    omega

theorem genus_free_face_deletion_injIn
    (C : GenusTruncatedCell q → Prop) (S : Finset (Cube (GenusVertex q)))
    (f : GenusTruncatedCell q) (t : QOld (cmpRel (GenusVertex q)))
    (hf : truncatedCellDimension f = 2) (ht : t.1.spx.card = 3)
    (htC : C (Sum.inl t))
    (hactive : ∀ d : QOld (cmpRel (GenusVertex q)), C (Sum.inl d) →
      d.1.spx.card = 3 → qCubeToCoordinate d.1 ∈ S)
    (hfree : Collapse.IsFree (spineInc (ASC.orderComplex (GenusVertex q))) S
      (truncatedFaceIndex f) (qCubeToCoordinate t.1)) :
    InjIn C (fun x => C x ∧ x ≠ f) := by
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
  apply injIn_delete_free_face htC hft hne
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

/-- In particular, deletion of an initially free two-face of the actual truncated block
reflects every null homotopy without a separate homotopy assumption. -/
theorem genus_initial_free_face_deletion_injIn
    (f : GenusTruncatedCell q) (t : QOld (cmpRel (GenusVertex q)))
    (hf : truncatedCellDimension f = 2) (ht : t.1.spx.card = 3)
    (hfree : Collapse.IsFree (spineInc (ASC.orderComplex (GenusVertex q)))
      (topCubes (ASC.orderComplex (GenusVertex q)))
      (truncatedFaceIndex f) (qCubeToCoordinate t.1)) :
    InjIn (fun _ : GenusTruncatedCell q => True) (fun x => x ≠ f) := by
  have h := genus_free_face_deletion_injIn q (fun _ => True)
    (topCubes (ASC.orderComplex (GenusVertex q))) f t hf ht trivial
    (fun d _ hd => by
      apply mem_topCubes.mpr
      refine ⟨?_, by simpa using hd⟩
      rw [freeSet_qCubeToCoordinate]
      intro a ha b hb _
      exact (isSimplex_cmpRel_iff.mp d.1.isSimplex) a ha b hb) hfree
  simpa only [true_and] using h

/-- The boundary of a later cube contains no face deleted in the prefix of the actual
chosen collapse. This prevents earlier steps from puncturing the next cube's boundary. -/
theorem genus_later_top_boundary_avoids_prefix_faces
    (left right : List (Cube (GenusVertex q) ×
      (Cube (GenusVertex q) ⊕ Finset (GenusVertex q))))
    (hl : genusChainCollapse q = left ++ right)
    (f : GenusTruncatedCell q) (t : QOld (cmpRel (GenusVertex q)))
    (ht : qCubeToCoordinate t.1 ∈ right.map Prod.fst)
    (hft : f ≤ Sum.inl t) : truncatedFaceIndex f ∉ left.map Prod.snd := by
  intro hf
  obtain ⟨p, hp, hpf⟩ := List.mem_map.mp hf
  obtain ⟨r, hr, hrt⟩ := List.mem_map.mp ht
  have hfullf : truncatedFaceIndex f ∈ (genusChainCollapse q).map Prod.snd := by
    rw [hl]
    exact List.mem_map.mpr ⟨p, List.mem_append.mpr (Or.inl hp), hpf⟩
  have hfullt : qCubeToCoordinate t.1 ∈ (genusChainCollapse q).map Prod.fst := by
    rw [hl]
    exact List.mem_map.mpr ⟨r, List.mem_append.mpr (Or.inr hr), hrt⟩
  have hdimf := genus_removedFace_dimension q f hfullf
  have hdimt : t.1.spx.card = 3 :=
    (genus_oldCell_removed_iff_dimension_three q t).mp hfullt
  have hL : t.1.spx ∈ (ASC.orderComplex (GenusVertex q)).faces := by
    intro a ha b hb _
    exact (isSimplex_cmpRel_iff.mp t.1.isSimplex) a ha b hb
  have hi := truncatedCell_inc_of_le f t hft hdimf hdimt hL
  have hc := genusChainCollapse_isPairCollapse q
  rw [hl] at hc
  have hn := hc.prefix_faces_avoid_suffix_tops hp hr
  rw [hpf, hrt] at hn
  exact hn hi

end FiniteChains.Davis.Genus
