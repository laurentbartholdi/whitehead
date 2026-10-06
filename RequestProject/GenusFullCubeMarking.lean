import RequestProject.SurfaceFullCubeFilling
import RequestProject.GenusSpinePresentation
import RequestProject.ZeroPi2Descent

/-! The actual surviving-spine marking contracts in the full cube quotient. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

noncomputable def oldToFullCube :
    Hom (orderCx (QOld (cmpRel (GenusVertex q))))
      (orderCx (QCube (cmpRel (GenusVertex q)))) :=
  orderCxMap Subtype.val (fun _ _ h => h)

noncomputable def markedSpineToFullCube :
    Hom (markedSpineCx q) (orderCx (QCube (cmpRel (GenusVertex q)))) :=
  Hom.comp (oldToFullCube q)
    (Hom.comp (genusSpineToOld q) (componentIncl (genusSpineCx q) (spineBase q)))

/-- The constructed map sends each actual capping loop to a null-homotopic loop. -/
theorem markedSpineToFullCube_mark_null (x : Fin q × Bool) :
    Htpy (orderCx (QCube (cmpRel (GenusVertex q))))
      ((markedSpineToFullCube q).onV (markedSpineBase q))
      ((markedSpineToFullCube q).onV (markedSpineBase q))
      (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1) [] := by
  have h := mapPath_htpy (oldToFullCube q) (spineMarkedLoop_toOld_htpy q x)
  have hf := surfaceFullCube_loop_null (cmpRel (GenusVertex q))
    (isPath_gSig q (x.1.val, x.2))
  have he : mapPath (oldToFullCube q)
      (mapPath (surfCx (cmpRel (GenusVertex q))) (gSig q (x.1.val, x.2))) =
      mapPath (orderCxMap (surfaceFullCube (cmpRel (GenusVertex q)))
        (surfaceFullCube_monotone _)) (gSig q (x.1.val, x.2)) := by
    simp only [mapPath, List.map_map]
    rfl
  rw (config := { transparency := .default }) [he] at h
  have hh := h.trans hf
  unfold markedSpineToFullCube
  rw (config := { transparency := .default }) [← mapPath_comp, ← mapPath_comp, markedSpineLoop_inclusion]
  exact hh

/-- Finite integral chains filling the exact capped-spine attaching loops. -/
theorem markedSpineToFullCube_mark_boundary (x : Fin q × Bool) :
    ∃ c : (orderCx (QCube (cmpRel (GenusVertex q)))).F →₀ ℤ,
      Comb.bdry2 _ c = pathChain
        (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1) := by
  simpa using (markedSpineToFullCube_mark_null q x).exists_boundary

noncomputable def spineFreeToFullCube :
    FreeGroup (SpinePresentationGen q) →*
      Pi1 (orderCx (QCube (cmpRel (GenusVertex q))))
        ((markedSpineToFullCube q).onV (markedSpineTree q).root) :=
  (pi1Map (markedSpineToFullCube q) (markedSpineTree q).root).comp
    (SpanningTree.freeToPi1 (markedSpineTree q))

/-- All actual capped presentation relators die in the full cube quotient. -/
theorem spineFreeToFullCube_capped_rel
    (m : SpinePresentationRel q ⊕ (Fin q × Bool)) :
    spineFreeToFullCube q (cappedSpinePresentation q m) = 1 := by
  cases m with
  | inl f =>
      change pi1Map (markedSpineToFullCube q) _
        (SpanningTree.freeToPi1 (markedSpineTree q)
          (SpanningTree.treeRel (markedSpineTree q) f)) = 1
      rw (config := { transparency := .default }) [SpanningTree.freeToPi1_treeRel, map_one]
  | inr x =>
      change pi1Map (markedSpineToFullCube q) _
        (SpanningTree.freeToPi1 (markedSpineTree q)
          (SpanningTree.pathWord (markedSpineTree q) (markedSpineLoop q x).1)) = 1
      rw (config := { transparency := .default }) [SpanningTree.freeToPi1_pathWord _ (markedSpineLoop q x).2]
      change pi1Map (markedSpineToFullCube q) _
        (pi1Conj ((markedSpineTree q).treePath_isPath (markedSpineBase q))
          (Pi1.mk (markedSpineLoop q x))) = 1
      rw (config := { transparency := .default }) [pi1Map_pi1Conj]
      have hz : pi1Map (markedSpineToFullCube q) (markedSpineBase q)
          (Pi1.mk (markedSpineLoop q x)) = 1 :=
        Quotient.sound (markedSpineToFullCube_mark_null q x)
      rw (config := { transparency := .default }) [hz, map_one]

/-- The genuine capped presentation maps to the full-cube fundamental group. -/
noncomputable def cappedPresentationToFullCube :
    PresGroup (cappedSpinePresentation q) →*
      Pi1 (orderCx (QCube (cmpRel (GenusVertex q))))
        ((markedSpineToFullCube q).onV (markedSpineTree q).root) :=
  QuotientGroup.lift _ (spineFreeToFullCube q) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨m, rfl⟩
    exact spineFreeToFullCube_capped_rel q m)

@[simp] theorem cappedPresentationToFullCube_mk (w : FreeGroup (SpinePresentationGen q)) :
    cappedPresentationToFullCube q (QuotientGroup.mk w) = spineFreeToFullCube q w := rfl

end FiniteChains.Davis.Genus
