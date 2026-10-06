import RequestProject.GenusSpineConnected
import RequestProject.GenusNamedSpineComparison
import RequestProject.ReceivedTreeFiberCoordinates
import RequestProject.StrictOrderPullbackHom
import RequestProject.UniversalOrderChainBridge
import RequestProject.GenusOldCoverSpineFaithfulness
import RequestProject.GenusOldCoverSpineGeneration

/-! The full pulled-back spine in the universal old cover has actual named
tree-cover coordinates before substitution. Pending final Lean verification.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000

namespace FiniteChains.Comb
universe u
variable {K Y Z : Complex2.{u}}

private theorem universal_pi1Map_comp (f : Hom K Y) (g : Hom Y Z) (a : K.V)
    (z : Pi1 K a) :
    pi1Map (g.comp f) a z = pi1Map g (f.onV a) (pi1Map f a z) := by
  refine Quotient.inductionOn z ?_
  intro p
  apply congrArg Pi1.mk
  apply Subtype.ext
  simp only [mapPath, Hom.comp, List.map_map, Function.comp_def]

private theorem universal_chain2_comp (f : Hom K Y) (g : Hom Y Z) (c : K.F →₀ ℤ) :
    chain2 (g.comp f) c = chain2 g (chain2 f c) := by
  change Finsupp.mapDomain (g.onF ∘ f.onF) c =
    Finsupp.mapDomain g.onF (Finsupp.mapDomain f.onF c)
  rw (config := { transparency := .default }) [Finsupp.mapDomain_comp]

end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
open scoped Classical
variable (q : ℕ) [NeZero q]

noncomputable def universalSpineToOld :
    Hom (markedSpineCx q) (orderCx (QOld (cmpRel (GenusVertex q)))) :=
  (genusSpineToOld q).comp (componentIncl (genusSpineCx q) (spineBase q))

noncomputable abbrev universalSpineOldBase :=
  (universalSpineToOld q).onV (markedSpineTree q).root

theorem universalSpineToOld_pi1_bijective :
    Function.Bijective (pi1Map (universalSpineToOld q) (markedSpineTree q).root) := by
  rw (config := { transparency := .default }) [markedSpineTree_root]
  have he : pi1Map (universalSpineToOld q) (markedSpineBase q) =
      (genusSpineToOldPi1Equiv q).toMonoidHom.comp (markedSpinePi1Equiv q).toMonoidHom := by
    apply MonoidHom.ext
    intro z
    exact universal_pi1Map_comp (componentIncl (genusSpineCx q) (spineBase q))
      (genusSpineToOld q) (markedSpineBase q) z
  rw (config := { transparency := .default }) [he]
  exact (genusSpineToOldPi1Equiv q).bijective.comp (markedSpinePi1Equiv q).bijective

/-- The receiver is the actual geometric fundamental-group equivalence,
with named generators folded back to the tree presentation. -/
noncomputable def universalSpineOldReceiver :
    PresGroup (namedSpinePresentation q) →*
      Pi1 (orderCx (QOld (cmpRel (GenusVertex q)))) (universalSpineOldBase q) :=
  (ReceivedTree.canonicalReceiver (markedSpineTree q) (universalSpineToOld q)).comp
    (namedSpineGroupEquiv q).symm.toMonoidHom

theorem universalSpineOldReceiver_bijective :
    Function.Bijective (universalSpineOldReceiver q) :=
  (universalSpineToOld_pi1_bijective q).comp
    ((spinePresentationPi1Equiv q).symm.bijective.comp (namedSpineGroupEquiv q).symm.bijective)

noncomputable def universalSpineWordReceiver :
    PresGroup (spinePresentation q) →* PresGroup (namedSpinePresentation q) :=
  (namedSpineGroupEquiv q).toMonoidHom

theorem universalSpineOldReceiver_compatible :
    (universalSpineOldReceiver q).comp (universalSpineWordReceiver q) =
      (pi1Map (universalSpineToOld q) (markedSpineTree q).root).comp
        (SpanningTree.presToPi1 (markedSpineTree q)) := by
  apply MonoidHom.ext
  intro z
  change (ReceivedTree.canonicalReceiver (markedSpineTree q) (universalSpineToOld q))
    ((namedSpineGroupEquiv q).symm ((namedSpineGroupEquiv q) z)) = _
  rw (config := { transparency := .default }) [MulEquiv.symm_apply_apply]
  rfl

noncomputable abbrev universalNamedSpineCover :=
  ReceivedTree.cover (markedSpineTree q) (universalSpineWordReceiver q)

noncomputable def universalNamedSpineComparison :
    Hom (universalNamedSpineCover q)
      (uCover (orderCx (QOld (cmpRel (GenusVertex q)))) (universalSpineOldBase q)) :=
  ReceivedTree.comparison (markedSpineTree q) (universalSpineToOld q)
    (universalSpineWordReceiver q) (universalSpineOldReceiver q)
    (universalSpineOldReceiver_compatible q)

noncomputable abbrev universalOldOrder :=
  UOrder (QOld (cmpRel (GenusVertex q))) (universalSpineOldBase q)

theorem universalOldEnd_isPosetCover :
    IsPosetCover (uOrderEnd (P := QOld (cmpRel (GenusVertex q)))
      (a := universalSpineOldBase q)) := by
  letI : Nonempty (GenusVertex q) := ⟨cV (gc q) (cyc (8 * q) 0)⟩
  exact uOrderEnd_isPosetCover isConnected_orderCx_qOld

noncomputable def universalReceivedOrderMap :
    Hom (universalNamedSpineCover q) (orderCx (universalOldOrder q)) :=
  uOrderHomInv.comp (universalNamedSpineComparison q)

noncomputable def universalReceivedStrictSpine :
    Hom (universalNamedSpineCover q) (strictOrderCx (GenusSpineCell q)) :=
  (componentIncl (genusSpineCx q) (spineBase q)).comp
    (ReceivedTree.projection (markedSpineTree q) (universalSpineWordReceiver q))

theorem universalReceived_spine_square :
    (orderCxMap uOrderEnd (universalOldEnd_isPosetCover q).mono).comp
      (universalReceivedOrderMap q) =
      (orderCxMap (genusSpineCellToOld q) (genusSpineCellToOld_monotone q)).comp
        ((strictOrderIncl (GenusSpineCell q)).comp (universalReceivedStrictSpine q)) := by
  apply Hom.ext'
  · funext a
    change uOrderEnd (uOrderHomInv.onV
      (ReceivedTree.receiverVertex (markedSpineTree q) (universalSpineToOld q)
        (universalSpineOldReceiver q) a.1 a.2)) = _
    rw (config := { transparency := .default }) [uOrderHomInv_vertex]
    exact ReceivedTree.receiverVertex_end _ _ _ _ _
  · funext e
    exact uOrderHomInv_edge_projection
      (ReceivedTree.receiverEdge (markedSpineTree q) (universalSpineToOld q)
        (universalSpineOldReceiver q) e.1 e.2)
  · funext t
    exact uOrderHomInv_face_projection
      (ReceivedTree.receiverFace (markedSpineTree q) (universalSpineToOld q)
        (universalSpineOldReceiver q) t.1 t.2)

noncomputable abbrev universalSpinePullback :=
  PosetCoverPullback (uOrderEnd (P := QOld (cmpRel (GenusVertex q)))
    (a := universalSpineOldBase q)) (genusSpineCellToOld q)

noncomputable def universalReceivedToPullback :
    Hom (universalNamedSpineCover q) (strictOrderCx (universalSpinePullback q)) :=
  strictOrderPullbackHom uOrderEnd (universalOldEnd_isPosetCover q)
    (genusSpineCellToOld q) (genusSpineCellToOld_monotone q)
    (universalReceivedOrderMap q) (universalReceivedStrictSpine q)
    (universalReceived_spine_square q)

private theorem universalPullbackFace_ext
    (t s : StrictOrdTri (universalSpinePullback q))
    (hp : (strictPullbackOriginal uOrderEnd (genusSpineCellToOld q)).onF t =
      (strictPullbackOriginal uOrderEnd (genusSpineCellToOld q)).onF s)
    (hs : (strictPullbackProjection uOrderEnd (universalOldEnd_isPosetCover q)
        (genusSpineCellToOld q) (genusSpineCellToOld_monotone q)).onF t =
      (strictPullbackProjection uOrderEnd (universalOldEnd_isPosetCover q)
        (genusSpineCellToOld q) (genusSpineCellToOld_monotone q)).onF s) : t = s := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact Prod.ext (congrArg (fun t => t.1.1) hp) (congrArg (fun t => t.1.1) hs)
  · apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext (congrArg (fun t => t.1.2.1) hp) (congrArg (fun t => t.1.2.1) hs)
    · apply Subtype.ext
      exact Prod.ext (congrArg (fun t => t.1.2.2) hp) (congrArg (fun t => t.1.2.2) hs)

/-- Every actual pulled-back spine face has named tree-cover coordinates.
The two ingredients are full-spine connectivity and the pre-substitution
geometric receiver equivalence. -/
theorem universalReceivedToPullback_onF_surjective :
    Function.Surjective (universalReceivedToPullback q).onF := by
  intro t
  let original := strictPullbackOriginal
    (uOrderEnd (P := QOld (cmpRel (GenusVertex q))) (a := universalSpineOldBase q))
    (genusSpineCellToOld q)
  let projection := strictPullbackProjection
    (uOrderEnd (P := QOld (cmpRel (GenusVertex q))) (a := universalSpineOldBase q))
    (universalOldEnd_isPosetCover q) (genusSpineCellToOld q) (genusSpineCellToOld_monotone q)
  obtain ⟨s, hs⟩ := markedSpine_component_onF_surjective q (projection.onF t)
  have ht : (uOrderFace (original.onF t)).1.2 =
      (universalSpineToOld q).onF s := by
    have hpair : (uOrderFace (original.onF t)).1.2 =
        (genusSpineToOld q).onF (projection.onF t) := by
      apply Subtype.ext
      exact Prod.ext t.1.1.2 (Prod.ext t.1.2.1.2 t.1.2.2.2)
    exact hpair.trans (congrArg (genusSpineToOld q).onF hs).symm
  obtain ⟨g, hg⟩ := ReceivedTree.receiverFace_fiber_surjective
    (markedSpineTree q) (universalSpineToOld q) (universalSpineOldReceiver q)
    (universalSpineOldReceiver_bijective q).2 s (uOrderFace (original.onF t)) ht
  refine ⟨(g, s), universalPullbackFace_ext q _ t ?_ ?_⟩
  · change (universalReceivedOrderMap q).onF (g, s) = original.onF t
    apply uOrderFace_injective
    change uOrderHom.onF (uOrderHomInv.onF
      (ReceivedTree.receiverFace (markedSpineTree q) (universalSpineToOld q)
        (universalSpineOldReceiver q) g s)) = uOrderFace (original.onF t)
    exact (homInv_onF_apply uOrderHom Function.bijective_id
      ⟨uOrderEdge_injective, uOrderEdge_surjective⟩
      ⟨uOrderFace_injective, uOrderFace_surjective⟩ _).trans hg
  · exact hs

/-- Arbitrary finite geometric two-chains can therefore be pulled back before substitution. -/
theorem universalReceivedToPullback_chain2_surjective :
    Function.Surjective (chain2 (universalReceivedToPullback q)) :=
  Finsupp.mapDomain_surjective (universalReceivedToPullback_onF_surjective q)

def universalSpinePullbackOldOrderIso :
    universalSpinePullback q ≃o OldCoveredSpine q
      (uOrderEnd (P := QOld (cmpRel (GenusVertex q))) (a := universalSpineOldBase q)) where
  toFun x := ⟨⟨(x.1.1, x.1.2.1), x.2⟩, x.1.2.2⟩
  invFun x := ⟨(x.1.1.1, ⟨x.1.1.2, x.2⟩), x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

noncomputable def universalReceivedToCoveredSpine :
    Hom (universalNamedSpineCover q)
      (strictOrderCx (OldCoveredSpine q
        (uOrderEnd (P := QOld (cmpRel (GenusVertex q))) (a := universalSpineOldBase q)))) :=
  (strictOrderCxMap (universalSpinePullbackOldOrderIso q)
    (universalSpinePullbackOldOrderIso q).strictMono).comp (universalReceivedToPullback q)

theorem universalReceivedToCoveredSpine_onF_surjective :
    Function.Surjective (universalReceivedToCoveredSpine q).onF := by
  intro t
  obtain ⟨c, hc⟩ := universalReceivedToPullback_onF_surjective q
    ((strictOrderCxMap (universalSpinePullbackOldOrderIso q).symm
      (universalSpinePullbackOldOrderIso q).symm.strictMono).onF t)
  refine ⟨c, ?_⟩
  change (strictOrderCxMap (universalSpinePullbackOldOrderIso q)
    (universalSpinePullbackOldOrderIso q).strictMono).onF
      ((universalReceivedToPullback q).onF c) = t
  rw (config := { transparency := .default }) [hc]
  apply Subtype.ext
  simp only [strictOrderCxMap, OrderIso.apply_symm_apply]

/-- This is the concrete pre-substitution chain lift needed for the normalized
marked reference filling. It applies to every finite chain on the full geometric spine. -/
theorem universalReceivedToCoveredSpine_chain2_surjective :
    Function.Surjective (chain2 (universalReceivedToCoveredSpine q)) :=
  Finsupp.mapDomain_surjective (universalReceivedToCoveredSpine_onF_surjective q)

/-- Keeping the underlying spine edge and its actual initial lift retains
both coordinates of a received edge. -/
noncomputable def universalCoveredSpineToStrictSpine :
    Hom (strictOrderCx (OldCoveredSpine q
      (uOrderEnd (P := QOld (cmpRel (GenusVertex q)))
        (a := universalSpineOldBase q)))) (strictOrderCx (GenusSpineCell q)) :=
  (strictPullbackProjection uOrderEnd (universalOldEnd_isPosetCover q)
    (genusSpineCellToOld q) (genusSpineCellToOld_monotone q)).comp
      (strictOrderCxMap (universalSpinePullbackOldOrderIso q).symm
        (universalSpinePullbackOldOrderIso q).symm.strictMono)

theorem universalReceivedToCoveredSpine_vertex_old
    (a : (universalNamedSpineCover q).V) :
    oldCoveredSpineToOld q uOrderEnd ((universalReceivedToCoveredSpine q).onV a) =
      (universalNamedSpineComparison q).onV a := by
  change uOrderHomInv.onV ((universalNamedSpineComparison q).onV a) = _
  exact uOrderHomInv_vertex _

theorem universalReceivedToCoveredSpine_onE_injective :
    Function.Injective (universalReceivedToCoveredSpine q).onE := by
  rintro ⟨g, e⟩ ⟨h, d⟩ he
  have hed : e = d := Subtype.ext
    (congrArg (universalCoveredSpineToStrictSpine q).onE he)
  subst d
  have hv : (universalReceivedToCoveredSpine q).onV
      ((universalNamedSpineCover q).src (g, e)) =
      (universalReceivedToCoveredSpine q).onV
        ((universalNamedSpineCover q).src (h, e)) := by
    rw (config := { transparency := .default }) [← (universalReceivedToCoveredSpine q).src_onE,
      ← (universalReceivedToCoveredSpine q).src_onE, he]
  have hv' := congrArg (oldCoveredSpineToOld q uOrderEnd) hv
  rw (config := { transparency := .default }) [universalReceivedToCoveredSpine_vertex_old,
    universalReceivedToCoveredSpine_vertex_old] at hv'
  have hg : g = h := ReceivedTree.receiverVertex_fiber_injective
    (markedSpineTree q) (universalSpineToOld q) (universalSpineOldReceiver q)
    (universalSpineOldReceiver_bijective q).1 ((markedSpineCx q).src e) hv'
  exact Prod.ext hg rfl

theorem universalReceivedToCoveredSpine_chain1_injective :
    Function.Injective (chain1 (universalReceivedToCoveredSpine q)) :=
  Finsupp.mapDomain_injective (universalReceivedToCoveredSpine_onE_injective q)

theorem universalReceivedCoveredChain_nerve_image
    (d : (universalNamedSpineCover q).F →₀ ℤ) :
    Nerve.cmap (oldCoveredSpineToOld q uOrderEnd)
      (ordNerveChain2 (ordStrictInclusion2
        (chain2 (universalReceivedToCoveredSpine q) d))) =
      universalNerveChain2 (chain2 (universalNamedSpineComparison q) d) := by
  have hfirst :
      (orderCxMap (oldCoveredSpineToOld q uOrderEnd)
        (oldCoveredSpineToOld_monotone q uOrderEnd)).comp
        ((strictOrderIncl _).comp (universalReceivedToCoveredSpine q)) =
        universalReceivedOrderMap q := by
    apply Hom.ext' <;> rfl
  change Nerve.cmap _ (ordNerveChain2 (chain2 (strictOrderIncl _)
    (chain2 (universalReceivedToCoveredSpine q) d))) =
    ordNerveChain2 (chain2 uOrderHomInv (chain2 (universalNamedSpineComparison q) d))
  rw (config := { transparency := .default }) [← ordNerveChain2_chain2 _ (oldCoveredSpineToOld_monotone q uOrderEnd)]
  apply congrArg ordNerveChain2
  have he := congrArg (fun k => chain2 k d) hfirst
  simpa only [universal_chain2_comp, universalReceivedOrderMap] using he

/-- The geometric adjustment lifts back to genuine pre-substitution tree
coordinates with its exact boundary preserved. The prescribed geometric
class is an explicit input here, rather than a claimed canonical choice. -/
theorem universalSpine_adjust_filling
    (d : (universalNamedSpineCover q).F →₀ ℤ)
    (z : Nerve.Ch (universalOldOrder q))
    (hz : z ∈ Nerve.Inc (universalOldOrder q))
    (hd : Nerve.lengthProjection 3 z = z)
    (hb : Nerve.bdry z = Nerve.bdry
      (Nerve.cmap (oldCoveredSpineToOld q uOrderEnd)
        (ordNerveChain2 (ordStrictInclusion2
          (chain2 (universalReceivedToCoveredSpine q) d))))) :
    ∃ d' : (universalNamedSpineCover q).F →₀ ℤ,
      Comb.bdry2 (universalNamedSpineCover q) d' = Comb.bdry2 (universalNamedSpineCover q) d ∧
      ∃ y ∈ Nerve.Inc (universalOldOrder q),
        z = Nerve.cmap (oldCoveredSpineToOld q uOrderEnd)
          (ordNerveChain2 (ordStrictInclusion2
            (chain2 (universalReceivedToCoveredSpine q) d'))) + Nerve.bdry y := by
  obtain ⟨c, hcb, y, hy, hzy⟩ := genus_old_cover_spine_adjust_filling q
    (uOrderEnd (P := QOld (cmpRel (GenusVertex q)))
      (a := universalSpineOldBase q)) (universalOldEnd_isPosetCover q)
    (chain2 (universalReceivedToCoveredSpine q) d) z hz hd hb
  obtain ⟨d', hd'⟩ := universalReceivedToCoveredSpine_chain2_surjective q c
  refine ⟨d', ?_, y, hy, ?_⟩
  · apply universalReceivedToCoveredSpine_chain1_injective q
    rw (config := { transparency := .default }) [← bdry2_chain2, ← bdry2_chain2, hd']
    exact hcb
  · rw (config := { transparency := .default }) [hd']
    exact hzy

/-- Cellular form of the actual geometric adjustment: equality of the
specified old-cover boundaries is sufficient, with no support premise added. -/
theorem universalSpine_adjust_to_chain
    (d : (universalNamedSpineCover q).F →₀ ℤ)
    (z : (uCover (orderCx (QOld (cmpRel (GenusVertex q))))
      (universalSpineOldBase q)).F →₀ ℤ)
    (hz : Comb.bdry2 _ z = chain1 (universalNamedSpineComparison q)
      (Comb.bdry2 (universalNamedSpineCover q) d)) :
    ∃ d' : (universalNamedSpineCover q).F →₀ ℤ,
      Comb.bdry2 (universalNamedSpineCover q) d' = Comb.bdry2 (universalNamedSpineCover q) d ∧
      ∃ y ∈ Nerve.Inc (universalOldOrder q),
        universalNerveChain2 z = universalNerveChain2
          (chain2 (universalNamedSpineComparison q) d') + Nerve.bdry y := by
  obtain ⟨d', hbd, y, hy, hzy⟩ := universalSpine_adjust_filling q d
    (universalNerveChain2 z) (universalNerveChain2_mem_inc z)
    (universalNerveChain2_lengthProjection z) (by
      rw (config := { transparency := .default }) [universalReceivedCoveredChain_nerve_image, universalNerveChain2_bdry,
        universalNerveChain2_bdry, bdry2_chain2, hz])
  refine ⟨d', hbd, y, hy, ?_⟩
  rwa [universalReceivedCoveredChain_nerve_image] at hzy

end FiniteChains.Davis.Genus
