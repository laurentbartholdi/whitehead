module

public import RequestProject.UniversalPathGauge
public import RequestProject.TreePresentation
public import RequestProject.ZeroPi2Descent

@[expose] public section

/-! The actual path-class cover gauge determined by a spanning tree and a cellular map. -/
namespace FiniteChains.Comb.SpanningTree
universe u
variable {K Y : Complex2.{u}} (T : SpanningTree K) (f : Hom K Y)

noncomputable def mappedTreeReference (a : K.V) : UV Y (f.onV T.root) :=
  extendList (mapPath f (T.treePath a)) (UV.base Y (f.onV T.root))

theorem mappedTreeReference_end (a : K.V) :
    endV (mappedTreeReference T f a) = f.onV a :=
  endV_extendList (isPath_mapPath f (T.treePath_isPath a))

/-- The geometric comparison reference paths have exactly the translation read by the tree. -/
theorem mappedTreeReference_path {a b : K.V} {p : List (K.E × Bool)}
    (hp : IsPath K.src K.tgt p a b) :
    extendList (mapPath f p) (mappedTreeReference T f a) =
      deckV (pi1Map f T.root (freeToPi1 T (pathWord T p)))
        (mappedTreeReference T f b) := by
  rw [freeToPi1_pathWord T hp]
  have h := extendList_reference_gauge
    (isPath_mapPath f (T.treePath_isPath a)) (isPath_mapPath f hp)
    (isPath_mapPath f (T.treePath_isPath b))
  have he : mapPath f (conjPath T p a b) =
      mapPath f (T.treePath a) ++ mapPath f p ++ revPath (mapPath f (T.treePath b)) := by
    rw [conjPath, mapPath_append, mapPath_append, mapPath_revPath]
  have hv : pi1Map f T.root (loopOf T hp) =
      Pi1.mk ⟨mapPath f (T.treePath a) ++ mapPath f p ++ revPath (mapPath f (T.treePath b)),
        ((isPath_mapPath f (T.treePath_isPath a)).append (isPath_mapPath f hp)).append
          (isPath_revPath (isPath_mapPath f (T.treePath_isPath b)))⟩ := by
    apply congrArg Pi1.mk
    apply Subtype.ext
    exact he
  rw [hv]
  exact h

end FiniteChains.Comb.SpanningTree
