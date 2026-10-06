module

public import RequestProject.GenusEquivariantCapFillings

@[expose] public section

/-! Linear cap fillings and their deck-forgetting formula on finitely supported coefficients. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

abbrev FullCubeDeck := Pi1 (orderCx (QCube (cmpRel (GenusVertex q)))) (fullCubeMarkBase q)

noncomputable def capCoefficientChain :
    (FullCubeDeck q × (Fin q × Bool) →₀ ℤ) →ₗ[ℤ] ((fullCubeMarkCover q).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun gx => equivariantCapChain q gx.1 gx.2)

noncomputable def capCoefficientBoundary :
    (FullCubeDeck q × (Fin q × Bool) →₀ ℤ) →ₗ[ℤ] ((fullCubeMarkCover q).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun gx => pathChain
    (uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q gx.2).1)
      (deckV gx.1 (UV.base _ (fullCubeMarkBase q)))))

/-- Linear combinations of genuine translated fillings have the exact lifted-loop boundary. -/
theorem capCoefficientChain_boundary (c : FullCubeDeck q × (Fin q × Bool) →₀ ℤ) :
    Comb.bdry2 _ (capCoefficientChain q c) = capCoefficientBoundary q c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add]
  | single gx n =>
      rw [capCoefficientChain, capCoefficientBoundary,
        Finsupp.linearCombination_single, Finsupp.linearCombination_single,
        map_smul, equivariantCapChain_boundary]

noncomputable def capAugmentedChain :
    (Fin q × Bool →₀ ℤ) →ₗ[ℤ]
      ((orderCx (QCube (cmpRel (GenusVertex q)))).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x =>
    hurewicz (orderCx (QCube (cmpRel (GenusVertex q)))) (fullCubeMarkBase q)
      (fullCubeBaseCapChain q x))

/-- Forgetting deck coordinates commutes with the constructed linear cap filling map. -/
theorem capCoefficientChain_hurewicz (c : FullCubeDeck q × (Fin q × Bool) →₀ ℤ) :
    hurewicz (orderCx (QCube (cmpRel (GenusVertex q)))) (fullCubeMarkBase q)
      (capCoefficientChain q c) = capAugmentedChain q (Finsupp.mapDomain Prod.snd c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      rw [map_add, map_add, hc, hd, Finsupp.mapDomain_add, map_add]
  | single gx n =>
      rw [capCoefficientChain, Finsupp.linearCombination_single, map_smul,
        equivariantCapChain_hurewicz, Finsupp.mapDomain_single, capAugmentedChain,
        Finsupp.linearCombination_single]

/-- The constructed homomorphism, with the proved tree-root/base equality transported. -/
noncomputable def cappedDeckToFullCube :
    PresGroup (cappedSpinePresentation q) →* FullCubeDeck q := by
  have h := cappedPresentationToFullCube q
  rw [markedSpineTree_root] at h
  exact h

noncomputable def cappedCapCoefficientChain :
    (PresGroup (cappedSpinePresentation q) × (Fin q × Bool) →₀ ℤ) →ₗ[ℤ]
      ((fullCubeMarkCover q).F →₀ ℤ) :=
  (capCoefficientChain q).comp (Finsupp.lmapDomain ℤ ℤ
    (fun gx => (cappedDeckToFullCube q gx.1, gx.2)))

/-- The actual capped-group coefficients have the exact full-cover lifted boundary. -/
theorem cappedCapCoefficientChain_boundary
    (c : PresGroup (cappedSpinePresentation q) × (Fin q × Bool) →₀ ℤ) :
    Comb.bdry2 _ (cappedCapCoefficientChain q c) =
      capCoefficientBoundary q (Finsupp.mapDomain
        (fun gx => (cappedDeckToFullCube q gx.1, gx.2)) c) :=
  capCoefficientChain_boundary q _

/-- Reindexing by the genuine group homomorphism preserves the augmentation formula. -/
theorem cappedCapCoefficientChain_hurewicz
    (c : PresGroup (cappedSpinePresentation q) × (Fin q × Bool) →₀ ℤ) :
    hurewicz (orderCx (QCube (cmpRel (GenusVertex q)))) (fullCubeMarkBase q)
      (cappedCapCoefficientChain q c) = capAugmentedChain q (Finsupp.mapDomain Prod.snd c) := by
  change hurewicz _ _ (capCoefficientChain q (Finsupp.mapDomain
    (fun gx => (cappedDeckToFullCube q gx.1, gx.2)) c)) = _
  rw [capCoefficientChain_hurewicz, ← Finsupp.mapDomain_comp]
  rfl

/-- The actual lift of the image of a chosen spine tree path. -/
noncomputable def fullCubeReferenceVertex (a : (markedSpineCx q).V) :
    UV (orderCx (QCube (cmpRel (GenusVertex q)))) (fullCubeMarkBase q) :=
  extendList (mapPath (markedSpineToFullCube q) ((markedSpineTree q).treePath a))
    (UV.base _ (fullCubeMarkBase q))

theorem fullCubeReferenceVertex_end (a : (markedSpineCx q).V) :
    endV (fullCubeReferenceVertex q a) = (markedSpineToFullCube q).onV a := by
  apply endV_extendList
  have hp := isPath_mapPath (markedSpineToFullCube q)
    ((markedSpineTree q).treePath_isPath a)
  rw [markedSpineTree_root] at hp
  exact hp

/-- Vertices indexed by the actual capped group, using the constructed comparison map. -/
noncomputable def cappedFullCubeVertex (g : PresGroup (cappedSpinePresentation q))
    (a : (markedSpineCx q).V) :
    UV (orderCx (QCube (cmpRel (GenusVertex q)))) (fullCubeMarkBase q) :=
  deckV (cappedDeckToFullCube q g) (fullCubeReferenceVertex q a)

theorem cappedFullCubeVertex_end (g : PresGroup (cappedSpinePresentation q))
    (a : (markedSpineCx q).V) :
    endV (cappedFullCubeVertex q g a) = (markedSpineToFullCube q).onV a := by
  rw [cappedFullCubeVertex, endV_deckV, fullCubeReferenceVertex_end]

/-- An old lifted face maps to an actual face in the full path-class cover. -/
noncomputable def cappedFullCubeOldFace (g : PresGroup (cappedSpinePresentation q))
    (f : (markedSpineCx q).F) : (fullCubeMarkCover q).F :=
  ⟨(cappedFullCubeVertex q g ((markedSpineCx q).base f),
      (markedSpineToFullCube q).onF f), by
    rw [cappedFullCubeVertex_end, (markedSpineToFullCube q).base_onF]⟩

end FiniteChains.Davis.Genus
