module

public import RequestProject.ClassicalCWChainSeeded

@[expose] public section

/-! Rebasing the constructed chain on prescribed original words and a
prescribed original tree. The base maps are genuine injective maps of
generators and two-cell labels, and their relator equation is proved.
Unverified source. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment PresModel Comb
open Set Topology
open scoped Classical
variable (D K : Whitehead.TwoComplex) {n : ℕ}
  (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C) (hconn : ∀ i, ConnectedSpace (C i : Set K))
  [Choices C] [TreeChoice K C]
  (T : SpanningTree (originalGraph D))
  (g : Hom (originalGraph D) (subcomplexGraph (C 0)))
  (hg : Function.Injective g.onE)
  (c : RelCWComplex.cell (Set.univ : Set D) 2 ↪ RelCWComplex.cell (C 0 : Set K) 2)
  (hw : ∀ j, Choices.cellWord 0 (c j) = (fixedGraphWord D j).map g)
  (ht : ∀ a, (chainTree K C hC hconn 0).isTree (g.onE a) ↔ T.isTree a)

def fixedBaseGen : FixedGen D T ↪ CanonicalGen K C hC hconn 0 :=
  StabilizedDiskPresentation.withDummy
    ⟨SpanningTree.nonTreeIncl ht, SpanningTree.nonTreeIncl_injective ht hg⟩

def fixedBaseCell : FixedRel D ↪ CanonicalRel K C 0 :=
  StabilizedDiskPresentation.withDummy c

include hw in
theorem fixedBase_relators (j : FixedRel D) :
    canonicalRelators K C hC hconn 0 (fixedBaseCell D K C c j) =
      FreeGroup.map (fixedBaseGen D K C hC hconn T g hg ht) (fixedRelators D T j) := by
  cases j with
  | inl j =>
      letI := subcomplexZeroSkeleton_discrete (C 0)
      change FreeGroup.map Sum.inl (FreeGroup.mk
        (((word C hC 0 (c j)).eraseTree (skeletonAttachingMap (C 0 : Set K) 1)
          (chainTree K C hC hconn 0)).loopWord)) = _
      rw (config := { transparency := .default }) [BoundaryWords.eraseTree_mk, word_zero, hw, BoundaryWords.loopWord_map,
        SpanningTree.pathWord_mapPath ht]
      change FreeGroup.map Sum.inl (FreeGroup.map (SpanningTree.nonTreeIncl ht) _) =
        FreeGroup.map (fixedBaseGen D K C hC hconn T g hg ht) (FreeGroup.map Sum.inl _)
      rw (config := { transparency := .default }) [FreeGroup.map.comp, FreeGroup.map.comp]
      rfl
  | inr u =>
      cases u
      rfl

def fixedPresChainTopFS
    (hkill : ∀ i : Fin n, Whitehead.KillsPi2
      (⟨Set.inclusion (hC (show i.castSucc ≤ i.succ from Nat.le_succ i.val)),
        continuous_inclusion _⟩ : C((C i.castSucc : Set K), (C i.succ : Set K)))) :
    PresChainTopFS (fixedRelators D T) n where
  gen r := CanonicalGen K C hC hconn (boundedStage n r)
  cell r := CanonicalRel K C (boundedStage n r)
  decGen _ := inferInstance
  rel r := canonicalRelators K C hC hconn (boundedStage n r)
  genIncl r := canonicalGenInclusion K C hC hconn (boundedStage_monotone n (Nat.le_succ r))
  genIncl_injective r := (canonicalGenInclusion K C hC hconn
    (boundedStage_monotone n (Nat.le_succ r))).injective
  cellIncl r := canonicalCellInclusion K C hC (boundedStage_monotone n (Nat.le_succ r))
  cellIncl_injective r := (canonicalCellInclusion K C hC
    (boundedStage_monotone n (Nat.le_succ r))).injective
  rel_incl r := canonicalRelators_natural K C hC hconn (boundedStage_monotone n (Nat.le_succ r))
  baseGen := fixedBaseGen D K C hC hconn T g hg ht
  baseGen_injective := (fixedBaseGen D K C hC hconn T g hg ht).injective
  baseCell := fixedBaseCell D K C c
  baseCell_injective := (fixedBaseCell D K C c).injective
  rel_base := fixedBase_relators D K C hC hconn T g hg c hw ht
  zero_pi2 := (canonicalPresChainTopFS K C hC hconn hkill).zero_pi2

def fixedPresChainFS
    (hkill : ∀ i : Fin n, Whitehead.KillsPi2
      (⟨Set.inclusion (hC (show i.castSucc ≤ i.succ from Nat.le_succ i.val)),
        continuous_inclusion _⟩ : C((C i.castSucc : Set K), (C i.succ : Set K)))) :
    PresChainFS (fixedRelators D T) n :=
  (fixedPresChainTopFS D K C hC hconn T g hg c hw ht hkill).toPresChainFS

end FiniteChains.ClassicalCW.ChainWords
