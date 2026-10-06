module

public import RequestProject.CombData
public import RequestProject.ClassicalGraphBoundaryWords

@[expose] public section

/-! Finite boundary words map naturally under actual graph maps, including
their four-side parametrizations. Unverified source. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
open scoped Classical unitInterval

namespace ContinuousEdgeWords
variable {G H : Comb.Complex2} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (h : Comb.Hom G H) (f : C(X, Y)) (v : G.V → X) (w : H.V → Y)
  (edge : ∀ e, Path (v (G.src e)) (v (G.tgt e)))
  (edge' : ∀ e, Path (w (H.src e)) (w (H.tgt e)))
  (hv : ∀ a, f (v a) = w (h.onV a))
  (he : ∀ e t, f (edge e t) = edge' (h.onE e) t)

include hv he in
theorem realize_map_apply (l : List (G.E × Bool)) {a b : G.V}
    (hl : Comb.IsPath G.src G.tgt l a b) (t : I) :
    f (realize G.src G.tgt v edge l hl t) =
      realize H.src H.tgt w edge' (Comb.mapPath h l) (Comb.isPath_mapPath h hl) t := by
  have same_start {a a' b : H.V} (m : List (H.E × Bool)) (ha : a = a')
      (h₁ : Comb.IsPath H.src H.tgt m a b) (h₂ : Comb.IsPath H.src H.tgt m a' b) (s : I) :
      realize H.src H.tgt w edge' m h₁ s = realize H.src H.tgt w edge' m h₂ s := by
    subst a'
    rfl
  induction l generalizing a t with
  | nil => exact hv a
  | cons g l ih =>
    change f (((germPath G.src G.tgt v edge g).cast _ _).trans
      (realize G.src G.tgt v edge l hl.2) t) =
      (((germPath H.src H.tgt w edge' (h.onE g.1, g.2)).cast _ _).trans
        (realize H.src H.tgt w edge' (Comb.mapPath h l) _) t)
    simp only [Path.trans_apply, Path.cast_coe]
    split_ifs
    · cases g with
      | mk e o => cases o <;> exact he e _
    · apply (ih hl.2 _).trans
      exact same_start (Comb.mapPath h l) (Comb.germTgt_onE h g).symm
        (Comb.isPath_mapPath h hl.2) (Comb.isPath_mapPath h hl).2 _

end ContinuousEdgeWords

namespace ClassicalGraphModel.BoundaryWords
open RelativeAttachment
variable {V W J K : Type} [TopologicalSpace V] [TopologicalSpace W]
  {r : BoundaryFamily J (Fin 1 → ℝ) → V}
  {s : BoundaryFamily K (Fin 1 → ℝ) → W}

def map (h : Comb.Hom (graphCx r) (graphCx s)) (b : BoundaryWords r) : BoundaryWords s where
  vertex := h.onV ∘ b.vertex
  word i := Comb.mapPath h (b.word i)
  isPath i := Comb.isPath_mapPath h (b.isPath i)

omit [TopologicalSpace V] [TopologicalSpace W] in
theorem map_comp {Z L : Type} [TopologicalSpace Z]
    {t : BoundaryFamily L (Fin 1 → ℝ) → Z}
    (h : Comb.Hom (graphCx r) (graphCx s))
    (k : Comb.Hom (graphCx s) (graphCx t)) (b : BoundaryWords r) :
    (b.map h).map k = b.map (k.comp h) := by
  cases b
  simp only [map, Comb.mapPath, List.map_map, Comb.Hom.comp]
  rfl

omit [TopologicalSpace V] [TopologicalSpace W] in
theorem loopWord_map (h : Comb.Hom (graphCx r) (graphCx s)) (b : BoundaryWords r) :
    (b.map h).loopWord = Comb.mapPath h b.loopWord := by
  simp only [loopWord, map, Comb.mapPath, Comb.revPath,
    List.append_eq, List.map_append, List.map_reverse, List.map_map]
  rfl

theorem boundaryMap_map (h : Comb.Hom (graphCx r) (graphCx s))
    (f : C(DiskAttachment r, DiskAttachment s))
    (hv : ∀ a, f (old r _ a) = old s _ (h.onV a))
    (he : ∀ e t, f (graphEdgePath r e t) = graphEdgePath s (h.onE e) t)
    (b : BoundaryWords r) :
    f.comp b.boundaryMap = (b.map h).boundaryMap := by
  ext x
  obtain ⟨⟨i, t⟩, hi⟩ := squareSideQuotient_surjective (unitBoundarySquareHomeomorph x)
  change f (b.squareMap (unitBoundarySquareHomeomorph x)) =
    (b.map h).squareMap (unitBoundarySquareHomeomorph x)
  change squareSideMap i t = unitBoundarySquareHomeomorph x at hi
  rw [← hi, squareMap_side, squareMap_side]
  exact ContinuousEdgeWords.realize_map_apply h f (old r _) (old s _)
    (graphEdgePath r) (graphEdgePath s) hv he (b.word i) (b.isPath i) t

end ClassicalGraphModel.BoundaryWords
end FiniteChains
