import RequestProject.ClassicalGraphRoseNaturality
import RequestProject.ContinuousEdgeWords
import RequestProject.TreePresentation

/-! The exact finite word read by collapsing a spanning tree. The word
is obtained by deleting the tree letters; the corresponding continuous
path homotopy removes precisely the resulting constant pauses. Unverified. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment ContinuousEdgeWords
open scoped Classical unitInterval
variable {V J : Type} [TopologicalSpace V] [DiscreteTopology V]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V) (hr : Continuous r)
  (T : Comb.SpanningTree (graphCx r))

def treeLetters : List (J × Bool) → List ({j : J // ¬T.isTree j} × Bool)
  | [] => []
  | g :: l => if h : T.isTree g.1 then treeLetters l
      else (⟨g.1, h⟩, g.2) :: treeLetters l

omit [TopologicalSpace V] [DiscreteTopology V] in
theorem treeLetters_append (l m : List (J × Bool)) :
    treeLetters r T (l ++ m) = treeLetters r T l ++ treeLetters r T m := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    by_cases h : T.isTree g.1 <;> simp only [List.cons_append, treeLetters, h,
      dite_true, dite_false, ih, List.cons_append]

omit [TopologicalSpace V] [DiscreteTopology V] in
theorem treeLetters_revPath (l : List (J × Bool)) :
    treeLetters r T (Comb.revPath (X := graphCx r) l) =
      Comb.revPath (X := graphCx (roseAttaching {j : J // ¬T.isTree j})) (treeLetters r T l) := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    rw [Comb.revPath_cons (X := graphCx r)]
    rw [treeLetters_append, ih]
    by_cases h : T.isTree g.1
    · simp only [treeLetters, Comb.revGerm, h, dite_true, List.append_nil]
    · simp only [treeLetters, Comb.revGerm, h, dite_false, Comb.revPath,
        List.reverse_cons, List.map_cons]

omit [TopologicalSpace V] [DiscreteTopology V] in
theorem treeLetters_mk (l : List (J × Bool)) :
    FreeGroup.mk (treeLetters r T l) = Comb.SpanningTree.pathWord T l := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    by_cases h : T.isTree g.1
    · rw [treeLetters, dif_pos h, Comb.SpanningTree.pathWord_cons T g l,
        Comb.SpanningTree.germWord_of_isTree T h, one_mul, ih]
    · rw [treeLetters, dif_neg h, Comb.SpanningTree.pathWord_cons]
      change FreeGroup.mk ([(⟨g.1, h⟩, g.2)] ++ treeLetters r T l) = _
      rw [← FreeGroup.mul_mk, ih]
      congr 1
      cases g with
      | mk j o => cases o <;> simp only [Comb.SpanningTree.germWord, dif_neg h] <;> rfl

theorem rose_word_isPath {A : Type} (l : List (A × Bool)) :
    Comb.IsPath (graphCx (roseAttaching A)).src (graphCx (roseAttaching A)).tgt l
      PUnit.unit PUnit.unit := by
  induction l with
  | nil => rfl
  | cons g l ih => cases g with | mk e o => cases o <;> exact ⟨rfl, ih⟩

def treeRoseWordPath (l : List (J × Bool)) :
    Path (roseVertex {j : J // ¬T.isTree j}) (roseVertex {j : J // ¬T.isTree j}) :=
  realize _ _ (old (roseAttaching _) _) (graphEdgePath (roseAttaching _))
    (treeLetters r T l) (rose_word_isPath _)

def collapsedWordPath (l : List (J × Bool)) {a b : V}
    (hl : Comb.IsPath (graphSrc r) (graphTgt r) l a b) :
    Path (roseVertex {j : J // ¬T.isTree j}) (roseVertex {j : J // ¬T.isTree j}) :=
  ((realize _ _ (old r _) (graphEdgePath r) l hl).map
    (graphRoseHomotopyEquiv r hr T).continuous).cast
      (graphRoseHomotopyEquiv_old r hr T a).symm
      (graphRoseHomotopyEquiv_old r hr T b).symm

def collapsedGermPath (g : J × Bool) :
    Path (roseVertex {j : J // ¬T.isTree j}) (roseVertex {j : J // ¬T.isTree j}) :=
  ((graphGermPath r g).map (graphRoseHomotopyEquiv r hr T).continuous).cast
    (graphRoseHomotopyEquiv_old r hr T _).symm
    (graphRoseHomotopyEquiv_old r hr T _).symm

theorem collapsedGermPath_tree (g : J × Bool) (h : T.isTree g.1) :
    collapsedGermPath r hr T g = Path.refl _ := by
  apply Path.ext
  funext t
  cases g with
  | mk j o =>
    cases o <;> exact graphRoseHomotopyEquiv_treePath r hr T ⟨j, h⟩ _

theorem collapsedGermPath_nonTree (g : J × Bool) (h : ¬T.isTree g.1) :
    collapsedGermPath r hr T g =
      germPath (graphSrc (roseAttaching _)) (graphTgt (roseAttaching _))
        (old (roseAttaching _) _) (graphEdgePath (roseAttaching _)) (⟨g.1, h⟩, g.2) := by
  apply Path.ext
  funext t
  cases g with
  | mk j o =>
    cases o <;> exact graphRoseHomotopyEquiv_nonTreeCell r hr T ⟨⟨j, h⟩, graphDiskHomeomorph _⟩

theorem collapsedWordPath_cons (g : J × Bool) (l : List (J × Bool)) {a b : V}
    (hl : Comb.IsPath (graphSrc r) (graphTgt r) (g :: l) a b) :
    collapsedWordPath r hr T (g :: l) hl =
      (collapsedGermPath r hr T g).trans (collapsedWordPath r hr T l hl.2) := by
  apply Path.ext
  funext t
  simp only [collapsedWordPath, collapsedGermPath, realize, Path.cast_coe,
    Path.map_coe, Function.comp_apply, Path.trans_apply]
  split_ifs
  · cases g with | mk j o => cases o <;> rfl
  · rfl

theorem collapsedWordPath_homotopic_treeWord (l : List (J × Bool)) {a b : V}
    (hl : Comb.IsPath (graphSrc r) (graphTgt r) l a b) :
    (collapsedWordPath r hr T l hl).Homotopic (treeRoseWordPath r T l) := by
  induction l generalizing a with
  | nil => exact Path.Homotopic.refl _
  | cons g l ih =>
    rw [collapsedWordPath_cons]
    by_cases hg : T.isTree g.1
    · rw [collapsedGermPath_tree r hr T g hg]
      have ht : treeRoseWordPath r T (g :: l) = treeRoseWordPath r T l := by
        simp only [treeRoseWordPath, treeLetters, dif_pos hg]
      rw [ht]
      exact ((Path.Homotopic.refl _).hcomp (ih hl.2)).trans (Path.Homotopic.refl_trans _)
    · rw [collapsedGermPath_nonTree r hr T g hg]
      have ht : treeRoseWordPath r T (g :: l) =
          (germPath (graphSrc (roseAttaching _)) (graphTgt (roseAttaching _))
            (old (roseAttaching _) _) (graphEdgePath (roseAttaching _))
              (⟨g.1, hg⟩, g.2)).trans (treeRoseWordPath r T l) := by
        simp only [treeRoseWordPath, treeLetters, dif_neg hg, realize]
        rfl
      rw [ht]
      exact (Path.Homotopic.refl _).hcomp (ih hl.2)

end FiniteChains.ClassicalGraphModel
