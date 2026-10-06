import RequestProject.GenusCappedLiftedPaths
import RequestProject.GenusFullCubeCoverFillings
import RequestProject.DeckChainTransport
import RequestProject.DavisUniversalThree

/-! The constructed two-chain comparison from the genuine capped tree cover. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {X Y : Complex2.{u}}
theorem pathChain_map_edges (f : X.E → Y.E) (p : List (X.E × Bool)) :
    pathChain (p.map (fun eb => (f eb.1, eb.2))) = Finsupp.mapDomain f (pathChain p) := by
  induction p with
  | nil => simp
  | cons e p ih =>
      rw [List.map_cons, pathChain_cons, pathChain_cons, ih, Finsupp.mapDomain_add]
      congr 1
      by_cases hb : e.2
      · simp [hb]
      · have hn : Finsupp.mapDomain f (-Finsupp.single e.1 (1 : ℤ)) =
            -Finsupp.mapDomain f (Finsupp.single e.1 (1 : ℤ)) := by
          simpa using (Finsupp.lmapDomain ℤ ℤ f).map_neg (Finsupp.single e.1 (1 : ℤ))
        simp [hb, hn]
end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
open scoped Classical
variable (q : ℕ) [NeZero q]

noncomputable abbrev rootedFullCover := uCover (orderCx (QCube (cmpRel (GenusVertex q))))
  ((markedSpineToFullCube q).onV (markedSpineTree q).root)
noncomputable abbrev cappedTreeCover := SpanningTree.treeCover (cappedSpineTree q)
  (relSub (cappedSpinePresentation q)) (by
    intro f
    rw [cappedSpineTree_rel]
    exact rel_mem_relSub (cappedSpinePresentation q) f)

noncomputable def rootedOldFace (g : PresGroup (cappedSpinePresentation q))
    (f : (markedSpineCx q).F) : (rootedFullCover q).F :=
  ⟨(rootedCappedFullVertex q g ((markedSpineCx q).base f),
    (markedSpineToFullCube q).onF f), by
      rw [rootedCappedFullVertex_end, (markedSpineToFullCube q).base_onF]⟩

noncomputable def rootedCoverChain1 :
    ((cappedTreeCover q).E →₀ ℤ) →ₗ[ℤ] ((rootedFullCover q).E →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun ge => rootedCappedFullEdge q ge.1 ge.2)

theorem rootedOldFace_boundary (g : PresGroup (cappedSpinePresentation q))
    (f : (markedSpineCx q).F) :
    Comb.bdry2 _ (Finsupp.single (rootedOldFace q g f) 1) =
      rootedCoverChain1 q (Comb.bdry2 _ (Finsupp.single (g, Sum.inl f) 1)) := by
  rw [bdry2_single, one_smul, bdry2_single, one_smul]
  change pathChain (uLiftPath ((orderCx (QCube (cmpRel (GenusVertex q)))).att
    ((markedSpineToFullCube q).onF f))
    (rootedCappedFullVertex q g ((markedSpineCx q).base f))) =
      Finsupp.mapDomain (fun ge => rootedCappedFullEdge q ge.1 ge.2)
        (pathChain (SpanningTree.liftK (cappedSpineTree q)
          (relSub (cappedSpinePresentation q)) ((markedSpineCx q).att f) g))
  rw [(markedSpineToFullCube q).att_onF]
  have hp := rootedCapped_liftPath q g ((markedSpineCx q).att_isLoop f)
  change _ = uLiftPath (mapPath (markedSpineToFullCube q) ((markedSpineCx q).att f)) _ at hp
  simp only [mapPath] at hp
  rw [← hp]
  exact pathChain_map_edges (X := cappedTreeCover q) (Y := rootedFullCover q)
    (fun ge => rootedCappedFullEdge q ge.1 ge.2) _

noncomputable def rootedBaseCapFilling (x : Fin q × Bool) : (rootedFullCover q).F →₀ ℤ :=
  fullCubeCoverCapChain q x
    (SpanningTree.mappedTreeReference (markedSpineTree q) (markedSpineToFullCube q)
      (markedSpineBase q))
    (SpanningTree.mappedTreeReference_end _ _ _)

noncomputable def rootedCapFilling (g : PresGroup (cappedSpinePresentation q))
    (x : Fin q × Bool) : (rootedFullCover q).F →₀ ℤ :=
  (univDeck _ ((markedSpineToFullCube q).onV (markedSpineTree q).root)).faceChains
    (cappedPresentationToFullCube q g) (rootedBaseCapFilling q x)

theorem rootedCapFilling_boundary (g : PresGroup (cappedSpinePresentation q))
    (x : Fin q × Bool) :
    Comb.bdry2 _ (rootedCapFilling q g x) =
      rootedCoverChain1 q (Comb.bdry2 _ (Finsupp.single (g, Sum.inr x) 1)) := by
  have hb := fullCubeCoverCapChain_boundary q x
    (SpanningTree.mappedTreeReference (markedSpineTree q) (markedSpineToFullCube q)
      (markedSpineBase q)) (SpanningTree.mappedTreeReference_end _ _ _)
  have ht := (univDeck _ ((markedSpineToFullCube q).onV (markedSpineTree q).root)).transport_filling
    (cappedPresentationToFullCube q g) (rootedBaseCapFilling q x) _ hb
  have he := uLiftPath_deckV (cappedPresentationToFullCube q g)
    (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1)
    (SpanningTree.mappedTreeReference (markedSpineTree q) (markedSpineToFullCube q)
      (markedSpineBase q)) ((markedSpineToFullCube q).onV (markedSpineBase q))
    (by rw [SpanningTree.mappedTreeReference_end]
        exact isPath_mapPath _ (markedSpineLoop q x).2)
  change Comb.bdry2 _ (rootedCapFilling q g x) = pathChain
    ((uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1)
      (SpanningTree.mappedTreeReference (markedSpineTree q) (markedSpineToFullCube q)
        (markedSpineBase q))).map
      (fun Eb => (deckE (cappedPresentationToFullCube q g) Eb.1, Eb.2))) at ht
  rw [← he] at ht
  rw [ht, bdry2_single, one_smul]
  change pathChain (uLiftPath (mapPath (markedSpineToFullCube q) (markedSpineLoop q x).1)
    (rootedCappedFullVertex q g (markedSpineBase q))) =
      Finsupp.mapDomain (fun ge => rootedCappedFullEdge q ge.1 ge.2)
        (pathChain (SpanningTree.liftK (cappedSpineTree q)
          (relSub (cappedSpinePresentation q)) (markedSpineLoop q x).1 g))
  rw [← rootedCapped_liftPath q g (markedSpineLoop q x).2]
  exact pathChain_map_edges (X := cappedTreeCover q) (Y := rootedFullCover q)
    (fun ge => rootedCappedFullEdge q ge.1 ge.2) _

noncomputable def rootedFaceComparison (gf : (cappedTreeCover q).F) :
    (rootedFullCover q).F →₀ ℤ :=
  match gf.2 with
  | .inl f => Finsupp.single (rootedOldFace q gf.1 f) 1
  | .inr x => rootedCapFilling q gf.1 x

noncomputable def rootedCoverChain2 :
    ((cappedTreeCover q).F →₀ ℤ) →ₗ[ℤ] ((rootedFullCover q).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (rootedFaceComparison q)

/-- The constructed comparison commutes with the boundary on every actual cover two-chain. -/
theorem rootedCoverChain2_boundary (c : (cappedTreeCover q).F →₀ ℤ) :
    Comb.bdry2 _ (rootedCoverChain2 q c) = rootedCoverChain1 q (Comb.bdry2 _ c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, map_add]
  | single gf n =>
      have hb : Comb.bdry2 _ (rootedFaceComparison q gf) =
          rootedCoverChain1 q (Comb.bdry2 _ (Finsupp.single gf 1)) := by
        obtain ⟨g, f | x⟩ := gf
        · exact rootedOldFace_boundary q g f
        · exact rootedCapFilling_boundary q g x
      rw [rootedCoverChain2, Finsupp.linearCombination_single, map_smul, hb]
      rw [bdry2_single, map_smul, bdry2_single, one_smul, map_smul]

/-- Every genuine capped-cover cycle has a degree-three filling after this comparison. -/
theorem rootedCoverCycle_fullCube_filling (c : (cappedTreeCover q).F →₀ ℤ)
    (hc : Comb.bdry2 (cappedTreeCover q) c = 0) :
    ∃ y : UOrdTet (QCube (cmpRel (GenusVertex q)))
        ((markedSpineToFullCube q).onV (markedSpineTree q).root) →₀ ℤ,
      uOrdBoundary3 y = rootedCoverChain2 q c := by
  apply exists_universal_bdry3_of_cycle_qCube
  rw [rootedCoverChain2_boundary, hc, map_zero]

end FiniteChains.Davis.Genus
