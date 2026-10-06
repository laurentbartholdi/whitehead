import RequestProject.GenusControlledCapFillings

import RequestProject.PositiveCornerChainExtraction
import RequestProject.GenusControlledFillingComparison

/-! Cap coefficients of actual capped-cover cycles bound on the actual genus surface. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem cornerSurfaceChain2_oldToFullCube
    (c : (orderCx (QOld (cmpRel (GenusVertex q)))).F →₀ ℤ) :
    cornerSurfaceChain2 (cmpRel (GenusVertex q)) (chain2 (oldToFullCube q) c) = 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw (config := { transparency := .default }) [map_add, map_add, hc, hd, add_zero]
  | single f n =>
      have hn := oldToFullCube_face_ne_corner q f
      change chain1 (cornerSurfaceMap _) (cornerChain2 (positiveCorner _)
        (Finsupp.mapDomain (oldToFullCube q).onF (Finsupp.single f n))) = 0
      rw (config := { transparency := .default }) [Finsupp.mapDomain_single, cornerChain2, Finsupp.linearCombination_single]
      simp [cornerTriangleEdge, hn]

theorem cornerSurfaceChain2_controlledCoverCap (x : Fin q × Bool) :
    cornerSurfaceChain2 (cmpRel (GenusVertex q))
      (hurewicz _ (fullCubeMarkBase q) (controlledCoverCap q x)) =
        pathChain (gSig q (x.1.val, x.2)) := by
  rw (config := { transparency := .default }) [controlledCoverCap_hurewicz, map_add, cornerSurfaceChain2_oldToFullCube,
    cornerSurfaceChain2_surfaceCornerFan, zero_add]

noncomputable def capSurfaceFace : (cappedSpineCx q).F →
    (orderCx (NeSpx (cmpRel (GenusVertex q)))).E →₀ ℤ
  | .inl _ => 0
  | .inr x => pathChain (gSig q (x.1.val, x.2))

noncomputable def capSurfaceChain2 : ((cappedSpineCx q).F →₀ ℤ) →ₗ[ℤ]
    ((orderCx (NeSpx (cmpRel (GenusVertex q)))).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (capSurfaceFace q)

theorem cornerSurfaceChain2_controlledAugmentedChain2 (c : (cappedSpineCx q).F →₀ ℤ) :
    cornerSurfaceChain2 (cmpRel (GenusVertex q)) (controlledAugmentedChain2 q c) =
      capSurfaceChain2 q c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw (config := { transparency := .default }) [map_add, map_add, map_add, hc, hd]
  | single f n =>
      rw (config := { transparency := .default }) [controlledAugmentedChain2, Finsupp.linearCombination_single, map_smul,
        capSurfaceChain2, Finsupp.linearCombination_single]
      apply congrArg (n • ·)
      obtain f | x := f
      · change cornerSurfaceChain2 _ (Finsupp.single ((markedSpineToFullCube q).onF f) 1) = 0
        have h := cornerSurfaceChain2_oldToFullCube q
          (Finsupp.single (((genusSpineToOld q).comp (componentIncl (genusSpineCx q) (spineBase q))).onF f) 1)
        change cornerSurfaceChain2 _ (Finsupp.mapDomain (oldToFullCube q).onF
          (Finsupp.single (((genusSpineToOld q).comp
            (componentIncl (genusSpineCx q) (spineBase q))).onF f) 1)) = 0 at h
        rw (config := { transparency := .default }) [Finsupp.mapDomain_single] at h
        exact h
      · exact cornerSurfaceChain2_controlledCoverCap q x

/-- The actual augmented capping loops of every capped-cover cycle form a surface boundary. -/
theorem capSurfaceCycle_boundary (c : (cappedTreeCover q).F →₀ ℤ)
    (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ d : (orderCx (NeSpx (cmpRel (GenusVertex q)))).F →₀ ℤ,
      Comb.bdry2 _ d = capSurfaceChain2 q (Finsupp.mapDomain Prod.snd c) := by
  obtain ⟨y, hy⟩ := controlledAugmentedCycle_boundary3 q c hc
  refine ⟨-cornerSurfaceChain3 _ y, ?_⟩
  rw (config := { transparency := .default }) [map_neg, ← cornerSurfaceChain2_ordBoundary3, hy,
    cornerSurfaceChain2_controlledAugmentedChain2]

end FiniteChains.Davis.Genus
