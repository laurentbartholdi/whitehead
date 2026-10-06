module

public import RequestProject.TruncatedCubePoset
public import RequestProject.OrderCxNatHtpy
public import RequestProject.StrictOrderComplex

@[expose] public section

/-! Based path comparison for the actual truncated face poset, before collapse. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

noncomputable def truncatedRetractionHom :
    Hom (orderCx (TruncatedCell A)) (orderCx (QOld A)) :=
  orderCxMap truncatedCellRetraction truncatedCellRetraction_monotone

noncomputable def truncatedSectionHom :
    Hom (orderCx (QOld A)) (orderCx (TruncatedCell A)) :=
  orderCxMap oldCellIncl oldCellIncl_monotone

/-- At a retained old cell the natural order homotopy fixes the basepoint. -/
theorem truncated_retraction_section_htpy (a : QOld A)
    {p : List ((orderCx (TruncatedCell A)).E × Bool)}
    (hp : IsPath (orderCx (TruncatedCell A)).src (orderCx (TruncatedCell A)).tgt
      p (oldCellIncl a) (oldCellIncl a)) :
    Htpy (orderCx (TruncatedCell A)) (oldCellIncl a) (oldCellIncl a)
      (mapPath truncatedSectionHom (mapPath truncatedRetractionHom p)) p := by
  let g : TruncatedCell A → TruncatedCell A := fun c =>
    oldCellIncl (truncatedCellRetraction c)
  have hg : Monotone g := oldCellIncl_monotone.comp truncatedCellRetraction_monotone
  have hh := htpy_loop_mapPath_le (f := id) monotone_id hg
    truncatedCell_le_retraction hp
  have hs := htpy_ordSelf_nil (oldCellIncl a)
  have hn := htpy_revPath (isPath_ordPos (le_refl (oldCellIncl a))) hs
  have hleft := hn.congr_append (isPath_nil' (oldCellIncl a))
    (hp.append (isPath_ordPos (le_refl (oldCellIncl a))))
  have hright := hs.congr_append hp (isPath_nil' (oldCellIncl a))
  simp only [List.nil_append, List.append_nil, revPath, List.reverse_nil,
    List.map_nil] at hleft hright
  have hcancel := hleft.trans hright
  have hnat : Htpy (orderCx (TruncatedCell A)) (oldCellIncl a) (oldCellIncl a)
      (mapPath truncatedSectionHom (mapPath truncatedRetractionHom p))
      ([ordNeg (le_refl (oldCellIncl a))] ++ p ++ [ordPos (le_refl (oldCellIncl a))]) := by
    simpa [g, truncatedSectionHom, truncatedRetractionHom, mapPath, orderCxMap,
      List.map_map, Function.comp_def] using hh
  exact hnat.trans (by simpa using hcancel)

theorem truncatedRetraction_pi1_injective (a : QOld A) :
    Function.Injective (pi1Map truncatedRetractionHom (oldCellIncl a)) := by
  rintro ⟨p⟩ ⟨q⟩ hpq
  have h : Htpy (orderCx (QOld A)) a a
      (mapPath truncatedRetractionHom p.1) (mapPath truncatedRetractionHom q.1) :=
    Quotient.exact hpq
  have hs := mapPath_htpy truncatedSectionHom h
  exact Quotient.sound
    ((truncated_retraction_section_htpy a p.2).symm.trans
      (hs.trans (truncated_retraction_section_htpy a q.2)))

theorem truncatedRetraction_pi1_surjective (a : QOld A) :
    Function.Surjective (pi1Map truncatedRetractionHom (oldCellIncl a)) := by
  rintro ⟨p⟩
  let lp : Loop (orderCx (TruncatedCell A)) (oldCellIncl a) :=
    ⟨mapPath truncatedSectionHom p.1, isPath_mapPath truncatedSectionHom p.2⟩
  refine ⟨Pi1.mk lp, ?_⟩
  apply congrArg Pi1.mk
  apply Subtype.ext
  simp [lp, truncatedSectionHom, truncatedRetractionHom, mapPath, orderCxMap,
    List.map_map, Function.comp_def]

/-- Truncating the positive corner preserves the based fundamental group. -/
noncomputable def truncatedRetractionPi1Equiv (a : QOld A) :
    Pi1 (orderCx (TruncatedCell A)) (oldCellIncl a) ≃* Pi1 (orderCx (QOld A)) a :=
  MulEquiv.ofBijective (pi1Map truncatedRetractionHom (oldCellIncl a))
    ⟨truncatedRetraction_pi1_injective a, truncatedRetraction_pi1_surjective a⟩

/-- The retraction also reflects null homotopies at a new cut-cell basepoint. -/
theorem truncatedRetraction_pi1_injective_at (a : TruncatedCell A) :
    Function.Injective (pi1Map truncatedRetractionHom a) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨p⟩ hp
  let g : TruncatedCell A → TruncatedCell A := fun c =>
    oldCellIncl (truncatedCellRetraction c)
  have hg : Monotone g := oldCellIncl_monotone.comp truncatedCellRetraction_monotone
  have hnat := htpy_loop_mapPath_le (f := id) monotone_id hg
    truncatedCell_le_retraction p.2
  have hnull : Htpy (orderCx (QOld A)) (truncatedCellRetraction a)
      (truncatedCellRetraction a) (mapPath truncatedRetractionHom p.1) [] :=
    Quotient.exact hp
  have hsec := mapPath_htpy truncatedSectionHom hnull
  have hgnil : Htpy (orderCx (TruncatedCell A)) (g a) (g a)
      (mapPath (orderCxMap g hg) p.1) [] := by
    simpa [g, truncatedSectionHom, truncatedRetractionHom, mapPath, orderCxMap,
      List.map_map, Function.comp_def] using hsec
  have hconj : Htpy (orderCx (TruncatedCell A)) (g a) (g a)
      ([ordNeg (truncatedCell_le_retraction a)] ++ p.1 ++
        [ordPos (truncatedCell_le_retraction a)]) [] := by
    simpa [mapPath, orderCxMap] using hnat.symm.trans hgnil
  have hstep := hconj.congr_append (isPath_ordPos (truncatedCell_le_retraction a))
    (isPath_ordNeg (truncatedCell_le_retraction a))
  have hc := htpy_ordPos_ordNeg (truncatedCell_le_retraction a)
  have hA := hc.congr_append (isPath_nil' a)
    (p.2.append (show IsPath (orderCx (TruncatedCell A)).src
      (orderCx (TruncatedCell A)).tgt
      [ordPos (truncatedCell_le_retraction a), ordNeg (truncatedCell_le_retraction a)]
      a a from ⟨rfl, rfl, rfl⟩))
  have hB := hc.congr_append p.2 (isPath_nil' a)
  have hstrip : Htpy (orderCx (TruncatedCell A)) a a
      ([ordPos (truncatedCell_le_retraction a)] ++
        ([ordNeg (truncatedCell_le_retraction a)] ++ p.1 ++
          [ordPos (truncatedCell_le_retraction a)]) ++
        [ordNeg (truncatedCell_le_retraction a)]) p.1 := by
    simpa [List.append_assoc] using hA.trans (by simpa using hB)
  have hkill : Htpy (orderCx (TruncatedCell A)) a a
      ([ordPos (truncatedCell_le_retraction a)] ++
        ([ordNeg (truncatedCell_le_retraction a)] ++ p.1 ++
          [ordPos (truncatedCell_le_retraction a)]) ++
        [ordNeg (truncatedCell_le_retraction a)]) [] := by
    exact hstep.trans (by simpa using hc)
  exact Quotient.sound (hstrip.symm.trans hkill)

theorem truncatedRetraction_pi1_surjective_at (a : TruncatedCell A) :
    Function.Surjective (pi1Map truncatedRetractionHom a) := by
  rintro ⟨p⟩
  let e := truncatedCell_le_retraction a
  let lp : Loop (orderCx (TruncatedCell A)) a :=
    ⟨[ordPos e] ++ mapPath truncatedSectionHom p.1 ++ [ordNeg e],
      ((isPath_ordPos e).append (isPath_mapPath truncatedSectionHom p.2)).append
        (isPath_ordNeg e)⟩
  refine ⟨Pi1.mk lp, Quotient.sound ?_⟩
  change Htpy (orderCx (QOld A)) (truncatedCellRetraction a) (truncatedCellRetraction a)
    (mapPath truncatedRetractionHom lp.val) p.val
  have hs := htpy_ordSelf_nil (truncatedCellRetraction a)
  have hn := htpy_revPath (isPath_ordPos (le_refl (truncatedCellRetraction a))) hs
  have hA := hs.congr_append (isPath_nil' (truncatedCellRetraction a))
    (p.2.append (isPath_ordNeg (le_refl (truncatedCellRetraction a))))
  have hB := hn.congr_append p.2 (isPath_nil' (truncatedCellRetraction a))
  simp only [List.nil_append, List.append_nil, revPath_nil] at hA hB
  have hh := hA.trans hB
  simpa [loopSetoid, ordPos, ordNeg, lp, e, truncatedRetractionHom, truncatedSectionHom, mapPath, orderCxMap,
    List.map_map, Function.comp_def, revPath, revGerm] using hh

/-- The actual retraction is a based fundamental-group isomorphism at every cell. -/
noncomputable def truncatedRetractionPi1EquivAt (a : TruncatedCell A) :
    Pi1 (orderCx (TruncatedCell A)) a ≃*
      Pi1 (orderCx (QOld A)) (truncatedCellRetraction a) :=
  MulEquiv.ofBijective (pi1Map truncatedRetractionHom a)
    ⟨truncatedRetraction_pi1_injective_at a, truncatedRetraction_pi1_surjective_at a⟩

end FiniteChains.Davis
