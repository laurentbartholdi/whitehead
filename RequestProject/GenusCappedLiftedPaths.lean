import RequestProject.GenusCappedRootedGauge
import RequestProject.GenusCappedSpine
import RequestProject.TreeCover

/-! Exact lifted-path comparison between the capped tree cover and the full cube cover. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

noncomputable def rootedCappedEdgeGerm
    (z : (PresGroup (cappedSpinePresentation q) × (markedSpineCx q).E) × Bool) :
    UE (orderCx (QCube (cmpRel (GenusVertex q))))
      ((markedSpineToFullCube q).onV (markedSpineTree q).root) × Bool :=
  (rootedCappedFullEdge q z.1.1 z.1.2, z.2)

/-- Comparison of an oriented lifted edge, including reverse traversal. -/
theorem rootedCapped_liftGerm (g : PresGroup (cappedSpinePresentation q))
    (eb : (markedSpineCx q).E × Bool) :
    rootedCappedEdgeGerm q
      (SpanningTree.liftGerm (cappedSpineTree q) (relSub (cappedSpinePresentation q)) g eb) =
      Comb.liftGerm (rootedCappedFullVertex q g
        (germSrc (markedSpineCx q).src (markedSpineCx q).tgt eb))
        ((markedSpineToFullCube q).onE eb.1, eb.2)
        (by rw [rootedCappedFullVertex_end, germSrc_onE]) := by
  obtain ⟨e, b⟩ := eb
  cases b with
  | true => rfl
  | false =>
      have h := rootedCappedFullVertex_path q g
        (isPath_single (X := markedSpineCx q) (e, false))
      have he : extend ((markedSpineToFullCube q).onE e, false)
          (rootedCappedFullVertex q g ((markedSpineCx q).tgt e)) =
          rootedCappedFullVertex q
            (g * QuotientGroup.mk (SpanningTree.germWord (markedSpineTree q) (e, false)))
            ((markedSpineCx q).src e) := by
        simpa only [mapPath, List.map_cons, List.map_nil, extendList_cons, extendList_nil,
          SpanningTree.pathWord_cons, SpanningTree.pathWord_nil, mul_one, germSrc, germTgt, ite_false, Bool.false_eq_true] using h
      apply Prod.ext
      · apply Subtype.ext
        apply Prod.ext
        · exact he.symm
        · rfl
      · rfl

/-- The comparison sends the entire genuine tree-cover lift to the actual path-class lift. -/
theorem rootedCapped_liftPath (g : PresGroup (cappedSpinePresentation q))
    {a b : (markedSpineCx q).V} {p : List ((markedSpineCx q).E × Bool)}
    (hp : IsPath (markedSpineCx q).src (markedSpineCx q).tgt p a b) :
    (SpanningTree.liftK (cappedSpineTree q) (relSub (cappedSpinePresentation q)) p g).map
      (rootedCappedEdgeGerm q) =
      uLiftPath (mapPath (markedSpineToFullCube q) p) (rootedCappedFullVertex q g a) := by
  induction p generalizing a g with
  | nil => rfl
  | cons eb p ih =>
      obtain ⟨ha, hp⟩ := hp
      subst a
      have hs : endV (rootedCappedFullVertex q g
          (germSrc (markedSpineCx q).src (markedSpineCx q).tgt eb)) =
          germSrc (orderCx (QCube (cmpRel (GenusVertex q)))).src
            (orderCx (QCube (cmpRel (GenusVertex q)))).tgt
            ((markedSpineToFullCube q).onE eb.1, eb.2) := by
        rw [rootedCappedFullVertex_end, germSrc_onE]
      have he : extend ((markedSpineToFullCube q).onE eb.1, eb.2)
          (rootedCappedFullVertex q g
            (germSrc (markedSpineCx q).src (markedSpineCx q).tgt eb)) =
          rootedCappedFullVertex q
            (g * QuotientGroup.mk (SpanningTree.germWord (markedSpineTree q) eb))
            (germTgt (markedSpineCx q).src (markedSpineCx q).tgt eb) := by
        have h := rootedCappedFullVertex_path q g (isPath_single (X := markedSpineCx q) eb)
        simpa only [mapPath, List.map_cons, List.map_nil, extendList_cons, extendList_nil,
          SpanningTree.pathWord_cons, SpanningTree.pathWord_nil, mul_one, germSrc, germTgt, ite_false, Bool.false_eq_true] using h
      rw [SpanningTree.liftK_cons, List.map_cons]
      change rootedCappedEdgeGerm q (SpanningTree.liftGerm _ _ g eb) :: _ =
        uLiftPath (((markedSpineToFullCube q).onE eb.1, eb.2) ::
          mapPath (markedSpineToFullCube q) p) _
      rw [uLiftPath_cons hs, he]
      apply congrArg₂ List.cons
      · exact rootedCapped_liftGerm q g eb
      · exact ih _ hp

end FiniteChains.Davis.Genus
