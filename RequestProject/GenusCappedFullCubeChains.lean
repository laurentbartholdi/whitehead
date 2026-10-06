module

public import RequestProject.GenusFullCubeMarking
public import RequestProject.GenusCappedSpine
public import RequestProject.UnivCoverIncl

@[expose] public section

/-! A constructed integral chain map from the capped spine into the full cube quotient. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
open scoped Classical
variable (q : ℕ) [NeZero q]

noncomputable def fullCubeCapFilling (x : Fin q × Bool) :
    (orderCx (QCube (cmpRel (GenusVertex q)))).F →₀ ℤ :=
  Classical.choose (markedSpineToFullCube_mark_boundary q x)

theorem fullCubeCapFilling_boundary (x : Fin q × Bool) :
    Comb.bdry2 _ (fullCubeCapFilling q x) =
      pathChain (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1) :=
  Classical.choose_spec (markedSpineToFullCube_mark_boundary q x)

noncomputable def cappedFullCubeChain1 :
    ((cappedSpineCx q).E →₀ ℤ) →ₗ[ℤ]
      ((orderCx (QCube (cmpRel (GenusVertex q)))).E →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (markedSpineToFullCube q).onE

noncomputable def cappedFullCubeFaceChain : (cappedSpineCx q).F →
    (orderCx (QCube (cmpRel (GenusVertex q)))).F →₀ ℤ
  | .inl f => Finsupp.single ((markedSpineToFullCube q).onF f) 1
  | .inr x => fullCubeCapFilling q x

noncomputable def cappedFullCubeChain2 :
    ((cappedSpineCx q).F →₀ ℤ) →ₗ[ℤ]
      ((orderCx (QCube (cmpRel (GenusVertex q)))).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (cappedFullCubeFaceChain q)

/-- The actual old cells and the chosen cap fillings commute with the cellular boundary. -/
theorem cappedFullCubeChain2_boundary (c : (cappedSpineCx q).F →₀ ℤ) :
    Comb.bdry2 _ (cappedFullCubeChain2 q c) =
      cappedFullCubeChain1 q (Comb.bdry2 (cappedSpineCx q) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, map_add]
  | single f n =>
      rw [cappedFullCubeChain2, Finsupp.linearCombination_single, map_smul,
        bdry2_single, map_smul]
      congr 1
      cases f with
      | inl f =>
          change Comb.bdry2 _ (Finsupp.single ((markedSpineToFullCube q).onF f) 1) =
            Finsupp.mapDomain (markedSpineToFullCube q).onE
              (pathChain ((markedSpineCx q).att f))
          rw [bdry2_single, one_smul, (markedSpineToFullCube q).att_onF f,
            pathChain_map]
      | inr x =>
          change Comb.bdry2 _ (fullCubeCapFilling q x) =
            Finsupp.mapDomain (markedSpineToFullCube q).onE
              (pathChain (markedSpineLoop q x).1)
          rw [fullCubeCapFilling_boundary]
          exact pathChain_map _ _

end FiniteChains.Davis.Genus
