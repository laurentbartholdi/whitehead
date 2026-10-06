module

public import RequestProject.GenusLiftedMarkingCorrection
public import RequestProject.OrderConeCoverFans
public import RequestProject.SurfaceFullCubeConeChains

@[expose] public section

/-! Controlled cap fillings in the actual full cube universal cover. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

noncomputable def markingCornerLift :
    UV (orderCx (QCube (cmpRel (GenusVertex q)))) (fullCubeMarkBase q) :=
  extend (coneRadial (surfaceFullCube (cmpRel (GenusVertex q)))
    (positiveCorner _) (positiveCorner_le_surface _) (gBase q), false)
    (UV.base _ (fullCubeMarkBase q))

theorem markingCornerLift_end : endV (markingCornerLift q) =
    positiveCorner (cmpRel (GenusVertex q)) :=
  endV_extend (by rfl)

theorem markingCornerLift_reference_base :
    coneCoverReference (surfaceFullCube (cmpRel (GenusVertex q)))
      (positiveCorner _) (positiveCorner_le_surface _) (markingCornerLift q) (gBase q) =
      UV.base _ (fullCubeMarkBase q) := by
  have h := extend_revGerm (X := orderCx (QCube (cmpRel (GenusVertex q))))
    (c := UV.base _ (fullCubeMarkBase q))
    (eb := (coneRadial (surfaceFullCube (cmpRel (GenusVertex q)))
      (positiveCorner _) (positiveCorner_le_surface _) (gBase q), false)) (by rfl)
  exact h

noncomputable def markingCoverConeFan (x : Fin q × Bool) : (fullCubeMarkCover q).F →₀ ℤ :=
  coneCoverFan (surfaceFullCube (cmpRel (GenusVertex q))) (surfaceFullCube_monotone _)
    (positiveCorner _) (positiveCorner_le_surface _) (markingCornerLift q)
    (markingCornerLift_end q) (pathChain (gSig q (x.1.val, x.2)))

theorem markingCoverConeFan_boundary (x : Fin q × Bool) :
    Comb.bdry2 (fullCubeMarkCover q) (markingCoverConeFan q x) =
      pathChain (uLiftPath (mapPath (orderCxMap (surfaceFullCube (cmpRel (GenusVertex q)))
        (surfaceFullCube_monotone _)) (gSig q (x.1.val, x.2)))
        (UV.base _ (fullCubeMarkBase q))) := by
  rw (config := { transparency := .default }) [markingCoverConeFan, coneCoverFan_loop_lift_boundary _ _ _ _ _ _
    (isPath_gSig q (x.1.val, x.2)), markingCornerLift_reference_base]

noncomputable def markingOldImage (x : Fin q × Bool) : (fullCubeMarkCover q).F →₀ ℤ :=
  chain2 (univLift _ (oldToFullCube q) (posQCube (gBase q))) (liftedMarkingCorrection q x)

noncomputable def controlledCoverCap (x : Fin q × Bool) : (fullCubeMarkCover q).F →₀ ℤ :=
  markingOldImage q x + markingCoverConeFan q x

/-- The old-cover correction and the controlled cone fan fill the exact lifted cap loop. -/
theorem controlledCoverCap_boundary (x : Fin q × Bool) :
    Comb.bdry2 (fullCubeMarkCover q) (controlledCoverCap q x) =
      pathChain (uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1)
        (UV.base _ (fullCubeMarkBase q))) := by
  rw (config := { transparency := .default }) [controlledCoverCap, map_add, markingOldImage, liftedMarkingCorrection_boundary, markingCoverConeFan_boundary]
  abel

/-- Its projection splits into old-block faces and the explicit positive-corner cone fan. -/
theorem controlledCoverCap_hurewicz (x : Fin q × Bool) :
    hurewicz _ (fullCubeMarkBase q) (controlledCoverCap q x) =
      chain2 (oldToFullCube q) (hurewicz _ (posQCube (gBase q)) (liftedMarkingCorrection q x)) +
        surfaceCornerFan (cmpRel (GenusVertex q)) (pathChain (gSig q (x.1.val, x.2))) := by
  rw (config := { transparency := .default }) [controlledCoverCap, map_add]
  apply congrArg₂ (· + ·)
  · exact hurewicz_univLift_chain2 (posQCube (gBase q)) (oldToFullCube q)
      (liftedMarkingCorrection q x)
  · rw (config := { transparency := .default }) [markingCoverConeFan, coneCoverFan_hurewicz]
    rfl

end FiniteChains.Davis.Genus
