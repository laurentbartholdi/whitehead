import RequestProject.SurfaceFullCubeConeChains
import RequestProject.GenusFullCubeMarking

/-! Concrete cap fillings split into an old-block marking correction and a positive cone fan. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

noncomputable def oldMarkingCorrection (x : Fin q × Bool) :
    (orderCx (QOld (cmpRel (GenusVertex q)))).F →₀ ℤ :=
  Classical.choose (spineMarkedLoop_toOld_htpy q x).exists_boundary

theorem oldMarkingCorrection_boundary (x : Fin q × Bool) :
    Comb.bdry2 _ (oldMarkingCorrection q x) =
      pathChain (mapPath (genusSpineToOld q) (spineMarkedLoop q x).1) -
      pathChain (mapPath (surfCx (cmpRel (GenusVertex q))) (gSig q (x.1.val, x.2))) :=
  Classical.choose_spec (spineMarkedLoop_toOld_htpy q x).exists_boundary

/-- The old marking correction plus the explicit positive-corner surface fan. -/
noncomputable def controlledCapFilling (x : Fin q × Bool) :
    (orderCx (QCube (cmpRel (GenusVertex q)))).F →₀ ℤ :=
  chain2 (oldToFullCube q) (oldMarkingCorrection q x) +
    surfaceCornerFan (cmpRel (GenusVertex q)) (pathChain (gSig q (x.1.val, x.2)))

/-- This split chain fills the exact surviving-spine capping loop. -/
theorem controlledCapFilling_boundary (x : Fin q × Bool) :
    Comb.bdry2 _ (controlledCapFilling q x) =
      pathChain (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1) := by
  have hsp : chain1 (oldToFullCube q)
      (pathChain (mapPath (genusSpineToOld q) (spineMarkedLoop q x).1)) =
      pathChain (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1) := by
    change Finsupp.mapDomain (oldToFullCube q).onE (pathChain _) = _
    rw (config := { transparency := .default }) [← pathChain_map]
    apply congrArg pathChain
    convert congrArg (fun p => mapPath (oldToFullCube q)
      (mapPath (genusSpineToOld q) p)) (markedSpineLoop_inclusion q x).symm using 1 <;>
      simp only [markedSpineToFullCube, mapPath, Hom.comp, List.map_map, Function.comp_def] <;> rfl
  have hsu : chain1 (oldToFullCube q)
      (pathChain (mapPath (surfCx (cmpRel (GenusVertex q))) (gSig q (x.1.val, x.2)))) =
      pathChain (mapPath (orderCxMap (surfaceFullCube (cmpRel (GenusVertex q)))
        (surfaceFullCube_monotone _)) (gSig q (x.1.val, x.2))) := by
    change Finsupp.mapDomain (oldToFullCube q).onE (pathChain _) = _
    rw (config := { transparency := .default }) [← pathChain_map]
    apply congrArg pathChain
    simp only [mapPath, List.map_map]
    rfl
  rw (config := { transparency := .default }) [controlledCapFilling, map_add, bdry2_chain2, oldMarkingCorrection_boundary,
    map_sub, hsp, hsu, surfaceCornerFan_loop_boundary _ (isPath_gSig q (x.1.val, x.2))]
  abel

/-- The explicit fan has no coefficients on triangles outside the positive-corner cone. -/
theorem surfaceCornerFan_eq_zero_off_corner
    (c : (orderCx (NeSpx (cmpRel (GenusVertex q)))).E →₀ ℤ)
    (t : (orderCx (QCube (cmpRel (GenusVertex q)))).F)
    (ht : t.1.1 ≠ positiveCorner (cmpRel (GenusVertex q))) :
    surfaceCornerFan (cmpRel (GenusVertex q)) c t = 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw (config := { transparency := .default }) [map_add, Finsupp.add_apply, hc, hd, add_zero]
  | single e n =>
      have he : coneEdgeTriangle (surfaceFullCube (cmpRel (GenusVertex q)))
          (surfaceFullCube_monotone _) (positiveCorner _) (positiveCorner_le_surface _) e ≠ t := by
        intro h
        apply ht
        exact (congrArg (fun z : (orderCx (QCube (cmpRel (GenusVertex q)))).F => z.1.1) h).symm
      rw (config := { transparency := .default }) [surfaceCornerFan, coneEdgeChain, Finsupp.linearCombination_single]
      simp [he]

/-- Restoring the corner does not turn an old face's first vertex into that corner. -/
theorem oldToFullCube_face_ne_corner
    (f : (orderCx (QOld (cmpRel (GenusVertex q)))).F) :
    ((oldToFullCube q).onF f).1.1 ≠ positiveCorner (cmpRel (GenusVertex q)) := by
  intro h
  apply f.1.1.2
  exact ⟨congrArg QCube.spx h, congrArg QCube.sgn h⟩

/-- The old-block summand has no coefficients on corner-first cone triangles. -/
theorem oldToFullCube_chain2_eq_zero_at_corner
    (c : (orderCx (QOld (cmpRel (GenusVertex q)))).F →₀ ℤ)
    (t : (orderCx (QCube (cmpRel (GenusVertex q)))).F)
    (ht : t.1.1 = positiveCorner (cmpRel (GenusVertex q))) :
    chain2 (oldToFullCube q) c t = 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw (config := { transparency := .default }) [map_add, Finsupp.add_apply, hc, hd, add_zero]
  | single f n =>
      have he : (oldToFullCube q).onF f ≠ t := by
        intro h
        apply oldToFullCube_face_ne_corner q f
        exact (congrArg (fun z : (orderCx (QCube (cmpRel (GenusVertex q)))).F => z.1.1) h).trans ht
      rw (config := { transparency := .default }) [chain2_apply, Finsupp.mapDomain_single]
      simp [he]

end FiniteChains.Davis.Genus
