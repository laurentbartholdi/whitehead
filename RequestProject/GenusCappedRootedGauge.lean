module

public import RequestProject.UniversalTreeGauge
public import RequestProject.GenusFullCubeMarking

@[expose] public section

/-! Exact lifted path translations for the genuine capped presentation group. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

noncomputable def rootedCappedFullVertex (g : PresGroup (cappedSpinePresentation q))
    (a : (markedSpineCx q).V) :
    UV (orderCx (QCube (cmpRel (GenusVertex q))))
      ((markedSpineToFullCube q).onV (markedSpineTree q).root) :=
  deckV (cappedPresentationToFullCube q g)
    (SpanningTree.mappedTreeReference (markedSpineTree q) (markedSpineToFullCube q) a)

theorem rootedCappedFullVertex_end (g : PresGroup (cappedSpinePresentation q))
    (a : (markedSpineCx q).V) :
    endV (rootedCappedFullVertex q g a) = (markedSpineToFullCube q).onV a := by
  rw [rootedCappedFullVertex, endV_deckV, SpanningTree.mappedTreeReference_end]

/-- Traversing any genuine spine path updates the comparison vertex by its capped-group word. -/
theorem rootedCappedFullVertex_path (g : PresGroup (cappedSpinePresentation q))
    {a b : (markedSpineCx q).V} {p : List ((markedSpineCx q).E × Bool)}
    (hp : IsPath (markedSpineCx q).src (markedSpineCx q).tgt p a b) :
    extendList (mapPath (markedSpineToFullCube q) p) (rootedCappedFullVertex q g a) =
      rootedCappedFullVertex q
        (g * QuotientGroup.mk (SpanningTree.pathWord (markedSpineTree q) p)) b := by
  unfold rootedCappedFullVertex
  rw [extendList_deckV, SpanningTree.mappedTreeReference_path _ _ hp,
    map_mul, cappedPresentationToFullCube_mk, deckV_mul]
  rfl

/-- Comparison edges are actual edges in the full path-class universal cover. -/
noncomputable def rootedCappedFullEdge (g : PresGroup (cappedSpinePresentation q))
    (e : (markedSpineCx q).E) :
    UE (orderCx (QCube (cmpRel (GenusVertex q))))
      ((markedSpineToFullCube q).onV (markedSpineTree q).root) :=
  ⟨(rootedCappedFullVertex q g ((markedSpineCx q).src e),
    (markedSpineToFullCube q).onE e), by
      rw [rootedCappedFullVertex_end, (markedSpineToFullCube q).src_onE]⟩

theorem rootedCappedFullEdge_src (g : PresGroup (cappedSpinePresentation q))
    (e : (markedSpineCx q).E) :
    uSrc (rootedCappedFullEdge q g e) =
      rootedCappedFullVertex q g ((markedSpineCx q).src e) := rfl

/-- The target incidence uses precisely the capped-group translation of this edge. -/
theorem rootedCappedFullEdge_tgt (g : PresGroup (cappedSpinePresentation q))
    (e : (markedSpineCx q).E) :
    uTgt (rootedCappedFullEdge q g e) = rootedCappedFullVertex q
      (g * QuotientGroup.mk (SpanningTree.germWord (markedSpineTree q) (e, true)))
      ((markedSpineCx q).tgt e) := by
  have h := rootedCappedFullVertex_path q g (isPath_single (X := markedSpineCx q) (e, true))
  simpa only [mapPath, List.map_cons, List.map_nil, extendList_cons, extendList_nil,
    SpanningTree.pathWord_cons, SpanningTree.pathWord_nil, mul_one, germSrc, germTgt, rootedCappedFullEdge, uTgt, ite_true] using h

end FiniteChains.Davis.Genus
