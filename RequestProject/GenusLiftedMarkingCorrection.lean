import RequestProject.LiftedHomotopyChains
import RequestProject.GenusEquivariantCapFillings

/-! Genuine old-block cover chains correcting the surviving-spine marking to its surface loop. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

noncomputable abbrev markingOldCover :=
  uCover (orderCx (QOld (cmpRel (GenusVertex q)))) (posQCube (gBase q))

/-- The marking correction is supported on actual old-block cover faces. -/
theorem exists_lifted_marking_correction (x : Fin q × Bool) :
    ∃ d : (markingOldCover q).F →₀ ℤ,
      Comb.bdry2 (fullCubeMarkCover q)
        (chain2 (univLift _ (oldToFullCube q) (posQCube (gBase q))) d) =
      pathChain (uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1)
        (UV.base _ (fullCubeMarkBase q))) -
      pathChain (uLiftPath (mapPath (orderCxMap (surfaceFullCube (cmpRel (GenusVertex q)))
        (surfaceFullCube_monotone _)) (gSig q (x.1.val, x.2)))
        (UV.base _ (fullCubeMarkBase q))) := by
  have hp := (spineMarkedLoop_toOld_htpy q x).symm.isPath
    (isPath_mapPath (surfCx _) (isPath_gSig q (x.1.val, x.2)))
  obtain ⟨d, hd⟩ := @exists_mapped_lifted_homotopy_chain
    (orderCx (QOld (cmpRel (GenusVertex q)))) (orderCx (QCube (cmpRel (GenusVertex q))))
    (posQCube (gBase q)) (oldToFullCube q)
    (UV.base (orderCx (QOld (cmpRel (GenusVertex q)))) (posQCube (gBase q)))
    (mapPath (genusSpineToOld q) (spineMarkedLoop q x).1)
    (mapPath (surfCx (cmpRel (GenusVertex q))) (gSig q (x.1.val, x.2)))
    (posQCube (gBase q)) hp (spineMarkedLoop_toOld_htpy q x)
  refine ⟨d, ?_⟩
  have he1 : mapPath (oldToFullCube q)
      (mapPath (genusSpineToOld q) (spineMarkedLoop q x).1) =
      mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1 := by
    convert congrArg (fun p => mapPath (oldToFullCube q)
      (mapPath (genusSpineToOld q) p)) (markedSpineLoop_inclusion q x).symm using 1 <;>
      simp only [markedSpineToFullCube, mapPath, Hom.comp, List.map_map, Function.comp_def] <;> rfl
  have he2 : mapPath (oldToFullCube q)
      (mapPath (surfCx (cmpRel (GenusVertex q))) (gSig q (x.1.val, x.2))) =
      mapPath (orderCxMap (surfaceFullCube (cmpRel (GenusVertex q)))
        (surfaceFullCube_monotone _)) (gSig q (x.1.val, x.2)) := by
    simp only [mapPath, List.map_map]
    rfl
  rw (config := { transparency := .default }) [he1, he2] at hd
  exact hd

noncomputable def liftedMarkingCorrection (x : Fin q × Bool) :
    (markingOldCover q).F →₀ ℤ :=
  Classical.choose (exists_lifted_marking_correction q x)

theorem liftedMarkingCorrection_boundary (x : Fin q × Bool) :
    Comb.bdry2 (fullCubeMarkCover q)
      (chain2 (univLift _ (oldToFullCube q) (posQCube (gBase q)))
        (liftedMarkingCorrection q x)) =
    pathChain (uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1)
      (UV.base _ (fullCubeMarkBase q))) -
    pathChain (uLiftPath (mapPath (orderCxMap (surfaceFullCube (cmpRel (GenusVertex q)))
      (surfaceFullCube_monotone _)) (gSig q (x.1.val, x.2)))
      (UV.base _ (fullCubeMarkBase q))) :=
  Classical.choose_spec (exists_lifted_marking_correction q x)

end FiniteChains.Davis.Genus
