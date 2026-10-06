module

public import RequestProject.ClassicalGraphRose
public import RequestProject.DiskFamilyMap

@[expose] public section

/-! Compatible spanning trees give an actual commuting graph-to-rose
square. The forward collapse is canonical on every characteristic
interval even though its homotopy inverse uses tree paths. Unverified. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
open scoped Classical
variable {V W J K : Type} [TopologicalSpace V] [TopologicalSpace W]
  [DiscreteTopology V] [DiscreteTopology W]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V) (hr : Continuous r)
  (s : BoundaryFamily K (Fin 1 → ℝ) → W) (hs : Continuous s)
  (T : Comb.SpanningTree (graphCx r)) (U : Comb.SpanningTree (graphCx s))
  (h : Comb.Hom (graphCx r) (graphCx s))
  (ht : ∀ j, U.isTree (h.onE j) ↔ T.isTree j)

def graphNonTreeMap : {j : J // ¬T.isTree j} → {k : K // ¬U.isTree k} :=
  fun j => ⟨h.onE j.val, fun hu => j.property ((ht j.val).mp hu)⟩

def graphRoseCombinatorialMap :
    Comb.Hom (graphCx (roseAttaching {j : J // ¬T.isTree j}))
      (graphCx (roseAttaching {k : K // ¬U.isTree k})) where
  onV := id
  onE := graphNonTreeMap r s T U h ht
  onF := Empty.elim
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF f := Empty.elim f
  att_onF f := Empty.elim f

def graphRoseMap : C(Rose {j : J // ¬T.isTree j}, Rose {k : K // ¬U.isTree k}) :=
  diskFamilyMap (roseAttaching _) (roseAttaching _) (ContinuousMap.id PUnit)
    (graphNonTreeMap r s T U h ht) (fun _ _ => rfl)

theorem graphRoseHomotopyEquiv_natural (f : C(DiskAttachment r, DiskAttachment s))
    (hv : ∀ v, f (old r (boundaryFamilyInclusion J _) v) =
      old s (boundaryFamilyInclusion K _) (h.onV v))
    (he : ∀ j x, f (cell r (boundaryFamilyInclusion J _) ⟨j, x⟩) =
      cell s (boundaryFamilyInclusion K _) ⟨h.onE j, x⟩) :
    (graphRoseMap r s T U h ht).comp (graphRoseHomotopyEquiv r hr T).toFun =
      (graphRoseHomotopyEquiv s hs U).toFun.comp f := by
  apply hom_ext r (boundaryFamilyInclusion J (Fin 1 → ℝ))
  · intro v
    change graphRoseMap r s T U h ht (graphRoseHomotopyEquiv r hr T (old _ _ v)) =
      graphRoseHomotopyEquiv s hs U (f (old _ _ v))
    rw [graphRoseHomotopyEquiv_old, hv]
    change _ = graphRoseHomotopyEquiv s hs U (old s _ (h.onV v))
    rw [graphRoseHomotopyEquiv_old]
    rfl
  · rintro ⟨j, x⟩
    change graphRoseMap r s T U h ht (graphRoseHomotopyEquiv r hr T (cell _ _ ⟨j, x⟩)) =
      graphRoseHomotopyEquiv s hs U (f (cell _ _ ⟨j, x⟩))
    rw [he]
    by_cases hj : T.isTree j
    · have hk := (ht j).mpr hj
      rw [graphRoseHomotopyEquiv_treeCell r hr T ⟨⟨j, hj⟩, x⟩,
        graphRoseHomotopyEquiv_treeCell s hs U ⟨⟨h.onE j, hk⟩, x⟩]
      rfl
    · have hk : ¬U.isTree (h.onE j) := fun hk => hj ((ht j).mp hk)
      rw [graphRoseHomotopyEquiv_nonTreeCell r hr T ⟨⟨j, hj⟩, x⟩,
        graphRoseHomotopyEquiv_nonTreeCell s hs U ⟨⟨h.onE j, hk⟩, x⟩]
      exact diskFamilyMap_cell (roseAttaching _) (roseAttaching _) (ContinuousMap.id PUnit)
        (graphNonTreeMap r s T U h ht) (fun _ _ => rfl) ⟨j, hj⟩ x

end FiniteChains.ClassicalGraphModel
