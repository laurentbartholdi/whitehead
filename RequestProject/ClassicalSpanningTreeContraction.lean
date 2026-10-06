import RequestProject.ClassicalGraphContraction
import Mathlib.Topology.Homotopy.Contractible

/-! A genuine continuous contraction of the disk realization of an arbitrary
spanning tree. Only each vertex's natural-number height is finite. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
open scoped unitInterval Topology Classical

variable {V J : Type} [TopologicalSpace V]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V) (T : Comb.SpanningTree (graphCx r))

def treeAttaching : BoundaryFamily {j : J // T.isTree j} (Fin 1 → ℝ) → V :=
  fun a => r ⟨a.1.val, a.2⟩

abbrev TreeSpace := DiskAttachment (treeAttaching r T)

def treeVertex (a : V) : TreeSpace r T :=
  old (treeAttaching r T) (boundaryFamilyInclusion {j : J // T.isTree j} _) a

private def treeUpPath (a : V) (ha : a ≠ T.root) :
    Path (treeVertex r T a) (treeVertex r T (T.parent a ha)) :=
  (graphGermPath (treeAttaching r T)
    (⟨(T.up a ha).1, T.isTree_up ha⟩, (T.up a ha).2)).cast
      (congrArg (treeVertex r T) (T.up_src a ha).symm) rfl

/-- Follow the finitely many chosen parent edges to the root. -/
def treeRootPath (a : V) : Path (treeVertex r T a) (treeVertex r T T.root) :=
  if ha : a = T.root then
    (Path.refl (treeVertex r T T.root)).cast (congrArg (treeVertex r T) ha) rfl
  else (treeUpPath r T a ha).trans (treeRootPath (T.parent a ha))
  termination_by T.ht a
  decreasing_by
    have h := T.ht_parent ha
    omega

@[simp] theorem treeRootPath_root :
    treeRootPath r T T.root = Path.refl (treeVertex r T T.root) := by
  rw [treeRootPath]
  simp

theorem treeRootPath_of_ne {a : V} (ha : a ≠ T.root) :
    treeRootPath r T a = (treeUpPath r T a ha).trans (treeRootPath r T (T.parent a ha)) := by
  rw [treeRootPath]
  simp only [dif_neg ha]

/-- Every retained edge is a chosen parent edge, so the actual vertex paths
have precisely the compatibility used by the cellwise contraction. -/
theorem treeRootPath_edge (j : {j : J // T.isTree j}) :
    treeRootPath r T (graphSrc (treeAttaching r T) j) =
      (graphEdgePath (treeAttaching r T) j).trans
        (treeRootPath r T (graphTgt (treeAttaching r T) j)) ∨
    treeRootPath r T (graphTgt (treeAttaching r T) j) =
      (graphEdgePath (treeAttaching r T) j).symm.trans
        (treeRootPath r T (graphSrc (treeAttaching r T) j)) := by
  obtain ⟨a, ha, he⟩ := (T.isTree_iff j.val).mp j.property
  cases hb : (T.up a ha).2 with
  | false =>
      have hg : T.up a ha = (j.val, false) := Prod.ext he hb
      have ha' : a = graphTgt (treeAttaching r T) j := by
        simpa [hg, Comb.germSrc_false, graphTgt, graphCx, treeAttaching] using (T.up_src a ha).symm
      have hp : T.parent a ha = graphSrc (treeAttaching r T) j := by
        simp only [Comb.SpanningTree.parent, hg, Comb.germTgt_false]
        rfl
      right
      apply Path.ext
      funext t
      have h := congrArg (fun p => p t) (treeRootPath_of_ne r T ha)
      have hu : ∀ s, treeUpPath r T a ha s = (graphEdgePath (treeAttaching r T) j).symm s := by
        intro s
        change graphGermPath (treeAttaching r T)
          (⟨(T.up a ha).1, T.isTree_up ha⟩, (T.up a ha).2) s = _
        have hpair :
            ((⟨(T.up a ha).1, T.isTree_up ha⟩, (T.up a ha).2) :
              {j : J // T.isTree j} × Bool) = (j, false) := by
          apply Prod.ext
          · exact Subtype.ext he
          · exact hb
        exact congrArg
          (fun g : {j : J // T.isTree j} × Bool => graphGermPath (treeAttaching r T) g s)
          hpair
      calc
        treeRootPath r T (graphTgt (treeAttaching r T) j) t = treeRootPath r T a t :=
          congrArg (fun v => treeRootPath r T v t) ha'.symm
        _ = ((treeUpPath r T a ha).trans (treeRootPath r T (T.parent a ha))) t := h
        _ = _ := by
          simp only [Path.trans_apply]
          split_ifs
          · exact hu _
          · exact congrArg (fun v => treeRootPath r T v _) hp
  | true =>
      have hg : T.up a ha = (j.val, true) := Prod.ext he hb
      have ha' : a = graphSrc (treeAttaching r T) j := by
        simpa [hg, Comb.germSrc_true, graphSrc, graphCx, treeAttaching] using (T.up_src a ha).symm
      have hp : T.parent a ha = graphTgt (treeAttaching r T) j := by
        simp only [Comb.SpanningTree.parent, hg, Comb.germTgt_true]
        rfl
      left
      apply Path.ext
      funext t
      have h := congrArg (fun p => p t) (treeRootPath_of_ne r T ha)
      have hu : ∀ s, treeUpPath r T a ha s = graphEdgePath (treeAttaching r T) j s := by
        intro s
        change graphGermPath (treeAttaching r T)
          (⟨(T.up a ha).1, T.isTree_up ha⟩, (T.up a ha).2) s = _
        have hpair :
            ((⟨(T.up a ha).1, T.isTree_up ha⟩, (T.up a ha).2) :
              {j : J // T.isTree j} × Bool) = (j, true) := by
          apply Prod.ext
          · exact Subtype.ext he
          · exact hb
        exact congrArg
          (fun g : {j : J // T.isTree j} × Bool => graphGermPath (treeAttaching r T) g s)
          hpair
      calc
        treeRootPath r T (graphSrc (treeAttaching r T) j) t = treeRootPath r T a t :=
          congrArg (fun v => treeRootPath r T v t) ha'.symm
        _ = ((treeUpPath r T a ha).trans (treeRootPath r T (T.parent a ha))) t := h
        _ = _ := by
          simp only [Path.trans_apply]
          split_ifs
          · exact hu _
          · exact congrArg (fun v => treeRootPath r T v _) hp

variable [DiscreteTopology V]

/-- The actual spanning-tree disk attachment is contracted to its literal
old root vertex. The entire tree may have arbitrarily many edges. -/
def treeContraction : ContinuousMap.Homotopy (ContinuousMap.id (TreeSpace r T))
    (ContinuousMap.const (TreeSpace r T) (treeVertex r T T.root)) :=
  graphContraction (treeAttaching r T) T.root (treeRootPath r T) (treeRootPath_edge r T)

@[simp] theorem treeContraction_vertex (t : I) (a : V) :
    treeContraction r T (t, treeVertex r T a) = treeRootPath r T a t := rfl

@[simp] theorem treeContraction_root (t : I) :
    treeContraction r T (t, treeVertex r T T.root) = treeVertex r T T.root := by
  rw [treeContraction_vertex, treeRootPath_root]
  rfl

theorem treeSpace_contractible : ContractibleSpace (TreeSpace r T) :=
  (contractible_iff_id_nullhomotopic _).mpr
    ⟨treeVertex r T T.root, ⟨treeContraction r T⟩⟩

/-- The collapse to one point has an actual inverse selecting the old root. -/
def treeHomotopyEquivUnit : ContinuousMap.HomotopyEquiv (TreeSpace r T) Unit where
  toFun := ContinuousMap.const _ ()
  invFun := ContinuousMap.const _ (treeVertex r T T.root)
  left_inv := ⟨(treeContraction r T).symm⟩
  right_inv := by
    have he : (ContinuousMap.const Unit () : C(Unit, Unit)) = ContinuousMap.id Unit := by
      ext x
    change ContinuousMap.Homotopic (ContinuousMap.const Unit ()) (ContinuousMap.id Unit)
    rw [he]

/-- The same specified collapse, with the universe-polymorphic singleton. -/
def treeHomotopyEquivPUnit : ContinuousMap.HomotopyEquiv (TreeSpace r T) PUnit where
  toFun := ContinuousMap.const _ PUnit.unit
  invFun := ContinuousMap.const _ (treeVertex r T T.root)
  left_inv := ⟨(treeContraction r T).symm⟩
  right_inv := by
    have he : (ContinuousMap.const PUnit PUnit.unit : C(PUnit, PUnit)) = ContinuousMap.id PUnit := by
      ext x
    change ContinuousMap.Homotopic (ContinuousMap.const PUnit PUnit.unit) (ContinuousMap.id PUnit)
    rw [he]

end FiniteChains.ClassicalGraphModel
