import RequestProject.HomeomorphContinuousMap
import RequestProject.OrderTriangleBoundaryWords
import RequestProject.ClassicalGraphTreeBoundaryWords
import RequestProject.ClassicalRoseWordNaturality
import RequestProject.ClassicalRoseWordReduction
import RequestProject.PresCircleWordParametrization
import RequestProject.PresCanonicalWords

/-! The canonical presentation of a strict order complex is an actual
homotopy model of its realization. The prescribed spanning tree is
transported to the literal interval graph without changing edge labels.
Pending the final Lean verification. -/

noncomputable section
open scoped Classical unitInterval Topology ContinuousMap
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.OrderTriangleWords
open RelativeAttachment ClassicalGraphModel PresModel SpanningTree
open OrderTriangleAttachment OrderEdgeAttachment CategoryTheory

variable (P : Type) [PartialOrder P]

local instance : DiscreteTopology (Vertices P) :=
  ClassicalCW.zeroSkeleton_discrete (X := orderNerveRealization P)

theorem graph_germSrc (g : StrictOrdEdge P × Bool) :
    germSrc (graphSrc (graphAttaching P)) (graphTgt (graphAttaching P)) g =
      vertexEquiv P (germSrc (strictOrderCx P).src (strictOrderCx P).tgt g) := by
  rcases g with ⟨e, b⟩
  cases b <;> simp only [germSrc, graphAttaching_source, graphAttaching_target] <;> rfl

theorem graph_germTgt (g : StrictOrdEdge P × Bool) :
    germTgt (graphSrc (graphAttaching P)) (graphTgt (graphAttaching P)) g =
      vertexEquiv P (germTgt (strictOrderCx P).src (strictOrderCx P).tgt g) := by
  rcases g with ⟨e, b⟩
  cases b <;> simp only [germTgt, graphAttaching_source, graphAttaching_target] <;> rfl

variable (T : SpanningTree (strictOrderCx P))

/-- Only the vertex names change. In particular the non-tree edge type
is definitionally the prescribed type `NonTree T`. -/
def graphTree : SpanningTree (graphCx (graphAttaching P)) where
  root := vertexEquiv P T.root
  ht v := T.ht ((vertexEquiv P).symm v)
  isTree := T.isTree
  up v hv := T.up ((vertexEquiv P).symm v) (by
    intro h
    apply hv
    simpa only [Equiv.apply_symm_apply] using congrArg (vertexEquiv P) h)
  ht_root := by simpa only [Equiv.symm_apply_apply] using T.ht_root
  ht_eq_zero := by
    intro v hv
    simpa only [Equiv.apply_symm_apply] using
      congrArg (vertexEquiv P) (T.ht_eq_zero _ hv)
  up_src := by
    intro v hv
    erw [graph_germSrc, T.up_src, Equiv.apply_symm_apply]
  up_ht := by
    intro v hv
    erw [graph_germTgt, Equiv.symm_apply_apply]
    exact T.up_ht _ _
  isTree_iff := by
    intro e
    constructor
    · intro he
      obtain ⟨v, hv, he⟩ := (T.isTree_iff e).mp he
      refine ⟨vertexEquiv P v, (fun h => hv ((vertexEquiv P).injective h)), ?_⟩
      simpa only [Equiv.symm_apply_apply] using he
    · rintro ⟨v, hv, he⟩
      refine (T.isTree_iff e).mpr ⟨(vertexEquiv P).symm v, ?_, he⟩
      intro h
      apply hv
      simpa only [Equiv.apply_symm_apply] using congrArg (vertexEquiv P) h

theorem graphTree_pathWord (l : List (StrictOrdEdge P × Bool)) :
    pathWord (graphTree P T) l = pathWord T l := rfl

def collapsedWords (t : StrictOrdTri P) : BoundaryWords (roseAttaching (NonTree T)) :=
  (words P t).eraseTree (graphAttaching P) (graphTree P T)

theorem collapsedWords_mk (t : StrictOrdTri P) :
    FreeGroup.mk (collapsedWords P T t).loopWord = treeRel T t := by
  change FreeGroup.mk ((words P t).eraseTree (graphAttaching P) (graphTree P T)).loopWord = _
  rw [BoundaryWords.eraseTree_mk, graphTree_pathWord, words_loopWord]
  rfl

def oneSkeletonRoseEquiv : OneSkeleton P ≃ₕ ClassicalGraphModel.Rose (NonTree T) :=
  (graphHomeomorph P).symm.toHomotopyEquiv.trans
    (graphRoseHomotopyEquiv (graphAttaching P) (graphAttaching P).continuous (graphTree P T))

def collapsedAttaching :
    C(BoundaryFamily (StrictOrdTri P) (Fin 2 → ℝ), ClassicalGraphModel.Rose (NonTree T)) :=
  (oneSkeletonRoseEquiv P T).toFun.comp (triangleAttaching P)

def collapsedCellBoundary (t : StrictOrdTri P) :
    C(UnitBoundary (Fin 2 → ℝ), ClassicalGraphModel.Rose (NonTree T)) :=
  (collapsedAttaching P T).comp
    ⟨Sigma.mk (β := fun _ : StrictOrdTri P => UnitBoundary (Fin 2 → ℝ)) t,
      by exact continuous_sigmaMk⟩

theorem collapsedCellBoundary_homotopic_words (t : StrictOrdTri P) :
    (collapsedCellBoundary P T t).Homotopic (collapsedWords P T t).boundaryMap := by
  have H := (ContinuousMap.Homotopic.refl
    (graphRoseHomotopyEquiv (graphAttaching P) (graphAttaching P).continuous
      (graphTree P T)).toFun).comp (graphBoundary_homotopic_words P t)
  exact H.trans ((words P t).collapse_homotopic_eraseTree
    (graphAttaching P) (graphAttaching P).continuous (graphTree P T))

variable (a : NonTree T)

theorem collapsedCellBoundary_homotopic_canonical (t : StrictOrdTri P) :
    (collapsedCellBoundary P T t).Homotopic
      (classicalPresCellBoundary (presCanonicalWords (treeRel T) a) t
        (presCanonicalWords_ne_nil (treeRel T) a)) := by
  have he : FreeGroup.mk (collapsedWords P T t).loopWord =
      FreeGroup.mk (presCanonicalWords (treeRel T) a t) :=
    (collapsedWords_mk P T t).trans (mk_presCanonicalWords (treeRel T) a t).symm
  exact (collapsedCellBoundary_homotopic_words P T t).trans
    ((boundaryWords_homotopic_classicalWord (collapsedWords P T t)).trans
      ((classicalRoseWordBoundary_homotopic_of_mk_eq he).trans
        (classicalPresWordAttaching_homotopic_read (presCanonicalWords (treeRel T) a) t
          (presCanonicalWords_ne_nil (treeRel T) a)).symm))

def collapsedAttachingCanonicalHomotopy :
    (collapsedAttaching P T).Homotopy
      (classicalPresWordAttaching (presCanonicalWords (treeRel T) a)
        (presCanonicalWords_ne_nil (treeRel T) a)) := by
  let H (t : StrictOrdTri P) := Classical.choice
    (collapsedCellBoundary_homotopic_canonical P T a t)
  let F : C(BoundaryFamily (StrictOrdTri P) (Fin 2 → ℝ),
      C(I, ClassicalGraphModel.Rose (NonTree T))) :=
    ⟨fun z => ((H z.1).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry z.2,
      continuous_sigma (fun t =>
        ((H t).toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry.continuous)⟩
  exact {
    toContinuousMap := F.uncurry.comp ⟨Prod.swap, continuous_swap⟩
    map_zero_left := fun z => (H z.1).apply_zero z.2
    map_one_left := fun z => (H z.1).apply_one z.2 }

/-- The comparison uses the actual CW attaching maps of every triangle,
not a homology or fundamental-group surrogate for a homotopy equivalence. -/
def canonicalTreeDiskRealizationEquiv [Nonempty P] [(nerve P).HasDimensionLE 2]
    (hP : IsConnected (orderCx P)) :
    ClassicalPresWordDisks (presCanonicalWords (treeRel T) a)
      (presCanonicalWords_ne_nil (treeRel T) a) ≃ₕ orderNerveRealization P :=
  (((triangleAttachmentRealizationHomeomorph P hP).symm.toHomotopyEquiv.trans
    (diskAttachmentBaseChangeHomotopyEquiv (triangleAttaching P)
      (oneSkeletonRoseEquiv P T))).trans
    (diskAttachingHomotopyEquiv (collapsedAttaching P T)
      (classicalPresWordAttaching (presCanonicalWords (treeRel T) a)
        (presCanonicalWords_ne_nil (treeRel T) a))
      (collapsedAttachingCanonicalHomotopy P T a))).symm

end FiniteChains.Comb.OrderTriangleWords
