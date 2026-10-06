import RequestProject.ClassicalCWChainConnectivity
import RequestProject.ClassicalGraphTreeWordNaturality
import RequestProject.DiskRoseMaps

/-! A simultaneous tree collapse of the actual graph-and-disk models.
The original two-cell labels and disk parameters are retained. Compatible
trees are constructed from connectedness, not supplied as a new input.
Unverified source. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment
open Set Topology
open scoped Classical ContinuousMap
variable (K : Whitehead.TwoComplex) {n : ℕ}
  (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C) (hconn : ∀ i, ConnectedSpace (C i : Set K))
  [Choices C]
  [TreeChoice K C]

omit [Choices C] [TreeChoice K C] in
theorem boundedTrees_compatible
    (T : ∀ r, Comb.SpanningTree (boundedGraph K C r))
    (hT : ∀ r e, (T (r + 1)).isTree ((boundedGraphInclusion K C hC r).onE e) ↔
      (T r).isTree e) {r s : ℕ} (hrs : r ≤ s)
    (e : (boundedGraph K C r).E) :
    (T s).isTree ((subcomplexGraphInclusion (hC (boundedStage_monotone n hrs))).onE e) ↔
      (T r).isTree e := by
  induction s, hrs using Nat.le_induction with
  | base => rfl
  | succ s hrs ih =>
      exact (hT s ((subcomplexGraphInclusion
        (hC (boundedStage_monotone n hrs))).onE e)).trans ih

include hconn in
theorem finiteGraphs_have_compatible_trees :
    ∃ T : ∀ i, Comb.SpanningTree (subcomplexGraph (C i)),
      (∀ S, TreeChoice.initial (K := K) (C := C) = some S → T 0 = S) ∧
      ∀ {i k : Fin (n + 1)} (hik : i ≤ k) e,
        (T k).isTree ((subcomplexGraphInclusion (hC hik)).onE e) ↔ (T i).isTree e := by
  obtain ⟨T, hT₀, hT⟩ := boundedGraphs_have_compatible_trees K C hC hconn
  have hs (i : Fin (n + 1)) : boundedStage n i.val = i := by
    apply Fin.ext
    exact Nat.min_eq_left (Nat.le_of_lt_succ i.isLt)
  let U (i : Fin (n + 1)) : Comb.SpanningTree (subcomplexGraph (C i)) := (hs i) ▸ T i.val
  have transport (a b : ℕ) (hab : a ≤ b) (i k : Fin (n + 1))
      (ha : boundedStage n a = i) (hb : boundedStage n b = k) (hik : i ≤ k) :
      ∀ e : (subcomplexGraph (C i)).E,
        (show Comb.SpanningTree (subcomplexGraph (C k)) from hb ▸ T b).isTree
            ((subcomplexGraphInclusion (hC hik)).onE e) ↔
          (show Comb.SpanningTree (subcomplexGraph (C i)) from ha ▸ T a).isTree e := by
    subst i
    subst k
    exact boundedTrees_compatible K C hC T hT hab
  refine ⟨U, ?_, ?_⟩
  · intro S hS
    exact hT₀ S hS
  · intro i k hik e
    exact transport i.val k.val (show i.val ≤ k.val from hik) i k (hs i) (hs k) hik e

def chainTree (i : Fin (n + 1)) : Comb.SpanningTree (subcomplexGraph (C i)) :=
  Classical.choose (finiteGraphs_have_compatible_trees K C hC hconn) i

theorem chainTree_zero (S : Comb.SpanningTree (subcomplexGraph (C 0)))
    (hS : TreeChoice.initial (K := K) (C := C) = some S) :
    chainTree K C hC hconn 0 = S :=
  (Classical.choose_spec (finiteGraphs_have_compatible_trees K C hC hconn)).1 S hS

theorem chainTree_compatible {i k : Fin (n + 1)} (hik : i ≤ k)
    (e : (subcomplexGraph (C i)).E) :
    (chainTree K C hC hconn k).isTree ((subcomplexGraphInclusion (hC hik)).onE e) ↔
      (chainTree K C hC hconn i).isTree e :=
  (Classical.choose_spec (finiteGraphs_have_compatible_trees K C hC hconn)).2 hik e

abbrev RoseGen (i : Fin (n + 1)) :=
  {e : (subcomplexGraph (C i)).E // ¬(chainTree K C hC hconn i).isTree e}

def roseGenInclusion {i k : Fin (n + 1)} (hik : i ≤ k) :
    RoseGen K C hC hconn i ↪ RoseGen K C hC hconn k where
  toFun e := ⟨(subcomplexGraphInclusion (hC hik)).onE e.val,
    fun ht => e.property ((chainTree_compatible K C hC hconn hik e.val).mp ht)⟩
  inj' := by
    intro e f hef
    apply Subtype.ext
    exact subcomplexGraphInclusion_injective_E (hC hik) (congrArg Subtype.val hef)

theorem roseGenInclusion_comp {i k l : Fin (n + 1)} (hik : i ≤ k) (hkl : k ≤ l)
    (e : RoseGen K C hC hconn i) :
    roseGenInclusion K C hC hconn hkl (roseGenInclusion K C hC hconn hik e) =
      roseGenInclusion K C hC hconn (hik.trans hkl) e := rfl

def graphCollapse (i : Fin (n + 1)) :
    DiskAttachment (skeletonAttachingMap (C i : Set K) 1) ≃ₕ
      ClassicalGraphModel.Rose (RoseGen K C hC hconn i) := by
  letI := subcomplexZeroSkeleton_discrete (C i)
  exact graphRoseHomotopyEquiv (skeletonAttachingMap (C i : Set K) 1)
    (skeletonAttachingMap (C i : Set K) 1).continuous (chainTree K C hC hconn i)

theorem graphCollapse_natural {i k : Fin (n + 1)} (hik : i ≤ k) :
    (diskRoseMap (roseGenInclusion K C hC hconn hik)).comp
        (graphCollapse K C hC hconn i).toFun =
      (graphCollapse K C hC hconn k).toFun.comp (subcomplexGraphDiskMap (hC hik)) := by
  letI := subcomplexZeroSkeleton_discrete (C i)
  letI := subcomplexZeroSkeleton_discrete (C k)
  have H := graphRoseHomotopyEquiv_natural
    (skeletonAttachingMap (C i : Set K) 1) (skeletonAttachingMap (C i : Set K) 1).continuous
    (skeletonAttachingMap (C k : Set K) 1) (skeletonAttachingMap (C k : Set K) 1).continuous
    (chainTree K C hC hconn i) (chainTree K C hC hconn k)
    (subcomplexGraphInclusion (hC hik)) (chainTree_compatible K C hC hconn hik)
    (subcomplexGraphDiskMap (hC hik)) (subcomplexGraphDiskMap_old (hC hik))
    (fun j x => subcomplexDiskMap_cell (hC hik) 1 j x)
  have he : graphRoseMap _ _ (chainTree K C hC hconn i) (chainTree K C hC hconn k)
      (subcomplexGraphInclusion (hC hik)) (chainTree_compatible K C hC hconn hik) =
      diskRoseMap (roseGenInclusion K C hC hconn hik) := by
    apply hom_ext (roseAttaching _) (boundaryFamilyInclusion _ (Fin 1 → ℝ))
    · intro u
      cases u
      rfl
    · rintro ⟨e, x⟩
      rw (config := { transparency := .default }) [graphRoseMap, diskFamilyMap_cell]
  rwa [he] at H

def collapsedAttaching (i : Fin (n + 1)) :
    C(BoundaryFamily (RelCWComplex.cell (C i : Set K) 2) (Fin 2 → ℝ),
      ClassicalGraphModel.Rose (RoseGen K C hC hconn i)) :=
  (graphCollapse K C hC hconn i).toFun.comp (wordAttaching C hC i)

theorem collapsedAttaching_natural {i k : Fin (n + 1)} (hik : i ≤ k)
    (j : RelCWComplex.cell (C i : Set K) 2) (a : UnitBoundary (Fin 2 → ℝ)) :
    diskRoseMap (roseGenInclusion K C hC hconn hik) (collapsedAttaching K C hC hconn i ⟨j, a⟩) =
      collapsedAttaching K C hC hconn k ⟨subcomplexCellInclusion (hC hik) 2 j, a⟩ := by
  have H := congrArg (fun f => f (wordAttaching C hC i ⟨j, a⟩))
    (graphCollapse_natural K C hC hconn hik)
  change _ = graphCollapse K C hC hconn k
    (subcomplexGraphDiskMap (hC hik) (wordAttaching C hC i ⟨j, a⟩)) at H
  rw (config := { transparency := .default }) [wordAttaching_natural] at H
  exact H

def collapsedDiskInclusion {i k : Fin (n + 1)} (hik : i ≤ k) :=
  diskFamilyMap (collapsedAttaching K C hC hconn i) (collapsedAttaching K C hC hconn k)
    (diskRoseMap (roseGenInclusion K C hC hconn hik))
    (subcomplexCellInclusion (hC hik) 2) (collapsedAttaching_natural K C hC hconn hik)

def collapsedDiskChange (i : Fin (n + 1)) :=
  diskAttachmentBaseChangeHomotopyEquiv (wordAttaching C hC i) (graphCollapse K C hC hconn i)

theorem collapsedDiskChange_natural {i k : Fin (n + 1)} (hik : i ≤ k) :
    (collapsedDiskInclusion K C hC hconn hik).comp (collapsedDiskChange K C hC hconn i).toFun =
      (collapsedDiskChange K C hC hconn k).toFun.comp (wordDiskInclusion K C hC hik) := by
  apply hom_ext (wordAttaching C hC i)
    (boundaryFamilyInclusion (RelCWComplex.cell (C i : Set K) 2) (Fin 2 → ℝ))
  · intro x
    have hleft := (congrArg (collapsedDiskInclusion K C hC hconn hik)
      (diskAttachmentBaseChangeHomotopyEquiv_old (wordAttaching C hC i)
        (graphCollapse K C hC hconn i) x)).trans
      (diskFamilyMap_old (collapsedAttaching K C hC hconn i) (collapsedAttaching K C hC hconn k)
        (diskRoseMap (roseGenInclusion K C hC hconn hik)) (subcomplexCellInclusion (hC hik) 2)
        (collapsedAttaching_natural K C hC hconn hik) (graphCollapse K C hC hconn i x))
    have hright := (congrArg (collapsedDiskChange K C hC hconn k)
      (diskFamilyMap_old (wordAttaching C hC i) (wordAttaching C hC k)
        (subcomplexGraphDiskMap (hC hik)) (subcomplexCellInclusion (hC hik) 2)
        (wordAttaching_natural K C hC hik) x)).trans
      (diskAttachmentBaseChangeHomotopyEquiv_old (wordAttaching C hC k)
        (graphCollapse K C hC hconn k) (subcomplexGraphDiskMap (hC hik) x))
    have hmid := congrArg (old (collapsedAttaching K C hC hconn k)
      (boundaryFamilyInclusion (RelCWComplex.cell (C k : Set K) 2) (Fin 2 → ℝ)))
      (congrArg (fun f => f x) (graphCollapse_natural K C hC hconn hik))
    exact hleft.trans (hmid.trans hright.symm)
  · rintro ⟨j, x⟩
    have hleft := (congrArg (collapsedDiskInclusion K C hC hconn hik)
      (diskAttachmentBaseChangeHomotopyEquiv_cell (wordAttaching C hC i)
        (graphCollapse K C hC hconn i) ⟨j, x⟩)).trans
      (diskFamilyMap_cell (collapsedAttaching K C hC hconn i) (collapsedAttaching K C hC hconn k)
        (diskRoseMap (roseGenInclusion K C hC hconn hik)) (subcomplexCellInclusion (hC hik) 2)
        (collapsedAttaching_natural K C hC hconn hik) j x)
    have hright := (congrArg (collapsedDiskChange K C hC hconn k)
      (diskFamilyMap_cell (wordAttaching C hC i) (wordAttaching C hC k)
        (subcomplexGraphDiskMap (hC hik)) (subcomplexCellInclusion (hC hik) 2)
        (wordAttaching_natural K C hC hik) j x)).trans
      (diskAttachmentBaseChangeHomotopyEquiv_cell (wordAttaching C hC k)
        (graphCollapse K C hC hconn k) ⟨subcomplexCellInclusion (hC hik) 2 j, x⟩)
    exact hleft.trans hright.symm

def collapsedDiskEquiv (i : Fin (n + 1)) :
    (C i : Set K) ≃ₕ DiskAttachment (collapsedAttaching K C hC hconn i) :=
  (wordDiskEquiv K C hC i).trans (collapsedDiskChange K C hC hconn i)

theorem collapsedDiskInclusion_killsPi2_iff {i k : Fin (n + 1)} (hik : i ≤ k) :
    Whitehead.KillsPi2 (collapsedDiskInclusion K C hC hconn hik) ↔
      Whitehead.KillsPi2 (⟨Set.inclusion (hC hik), continuous_inclusion (hC hik)⟩ :
        C((C i : Set K), (C k : Set K))) := by
  rw (config := { transparency := .default }) [← wordDiskInclusion_killsPi2_iff K C hC hik]
  apply Whitehead.killsPi2_homotopyEquiv_square_iff
    (collapsedDiskChange K C hC hconn i) (collapsedDiskChange K C hC hconn k)
  rw (config := { transparency := .default }) [collapsedDiskChange_natural]

end FiniteChains.ClassicalCW.ChainWords
