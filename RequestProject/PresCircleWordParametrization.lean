import RequestProject.HomeomorphContinuousMap
import RequestProject.RelatorCircleTraversalWord
import RequestProject.PresRoseAffineWordReading
import RequestProject.PresClassicalDiskComparison

/-! Match the canonical relator-circle parametrization with the actual
finite edge-word attaching loop. Both sides are maps of the genuine disk
boundary and the comparison is an actual homotopy. Pending verification. -/

noncomputable section
open scoped Classical unitInterval Topology
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb RelativeAttachment ContinuousEdgeWords ClassicalGraphModel

variable {A J : Type} (w : J → List (A × Bool)) (j : J) (hn : 0 < (w j).length)

def presReadTraversal : Path (orderRoseBase A) (orderRoseBase A) where
  toFun t := presCircleWordMap w j (relatorCircleTraversal w j hn t)
  continuous_toFun := (presCircleWordMap w j).continuous.comp
    (relatorCircleTraversal w j hn).continuous
  source' := by
    rw (config := { transparency := .default }) [(relatorCircleTraversal w j hn).source]
    exact realizedMap_vertex (fun c : RelatorCircle w j => aFun w c.val)
      (fun _ _ h => aFun_monotone w h) (relatorCircleEnumeration w j hn 0)
  target' := by
    rw (config := { transparency := .default }) [(relatorCircleTraversal w j hn).target]
    exact realizedMap_vertex (fun c : RelatorCircle w j => aFun w c.val)
      (fun _ _ h => aFun_monotone w h) (relatorCircleEnumeration w j hn 0)

theorem presReadTraversal_homotopic_word :
    (presReadTraversal w j hn).Homotopic (orderRoseRead (w j)) := by
  let f : C(orderNerveRealization (TCirc w), orderNerveRealization (Rose A)) :=
    (orderNerveRealizationMap (aFun w) (aFun_monotone w)).hom
  have hb : orderRoseBase A = f (orderNerveRealizationVertex (circleWordVertex w j hn 0)) :=
    (realizedMap_vertex (aFun w) (aFun_monotone w) (circleWordVertex w j hn 0)).symm
  have H := ((circleFullLoop_homotopic_word w j hn).map f).pathCast hb hb
  have hleft : ((circleFullLoop w j hn).map f.continuous).cast hb hb =
      presReadTraversal w j hn := by
    apply Path.ext
    funext t
    change orderNerveRealizationMap (aFun w) (aFun_monotone w) (circleFullLoop w j hn t) = _
    rw (config := { transparency := .default }) [← circleTraversal_to_full, orderNerveRealizationMap_comp]
    rfl
  have hright : ((affineOrderWordPath (circLoop w j) (circleWordValid w j hn)).map f.continuous).cast hb hb =
      affineOrderWordPath (roseWord (w j)) (roseWord_valid (w j)) := by
    apply Path.ext
    funext t
    change orderNerveRealizationMap (aFun w) (aFun_monotone w)
      (affineOrderWordPath (circLoop w j) (circleWordValid w j hn) t) = _
    rw (config := { transparency := .default }) [affineOrderWordPath_map]
    have wordEq {l m : List ((orderCx (Rose A)).E × Bool)} {a b : Rose A}
        (hl : IsPath (orderCx (Rose A)).src (orderCx (Rose A)).tgt l a b)
        (hm : IsPath (orderCx (Rose A)).src (orderCx (Rose A)).tgt m a b) (he : l = m) :
        affineOrderWordPath l hl t = affineOrderWordPath m hm t := by
      subst m
      rfl
    exact wordEq _ _ (mapPath_aFun_circLoop w j)
  rw (config := { transparency := .default }) [hleft, hright] at H
  exact H.trans (roseWord_homotopic_read (w j))

def classicalPresReadTraversal : Path (roseVertex A) (roseVertex A) :=
  ((presReadTraversal w j hn).map (orderRoseRealizationHomeomorph A).continuous).cast
    (orderRoseRealizationHomeomorph_base A).symm (orderRoseRealizationHomeomorph_base A).symm

theorem classicalPresReadTraversal_homotopic_word :
    (classicalPresReadTraversal w j hn).Homotopic (classicalRoseRead (w j)) := by
  have H := ((presReadTraversal_homotopic_word w j hn).map
    (orderRoseRealizationHomeomorph A).toContinuousMap).pathCast
    (orderRoseRealizationHomeomorph_base A).symm (orderRoseRealizationHomeomorph_base A).symm
  have he : ((orderRoseRead (w j)).map (orderRoseRealizationHomeomorph A).continuous).cast
      (orderRoseRealizationHomeomorph_base A).symm (orderRoseRealizationHomeomorph_base A).symm =
        classicalRoseRead (w j) := by
    apply Path.ext
    funext t
    exact orderRoseRead_classical (w j) t
  rwa [he] at H

variable (hw : ∀ j, w j ≠ [])

def classicalPresCellBoundary : C(UnitBoundary (Fin 2 → ℝ), ClassicalGraphModel.Rose A) :=
  (classicalPresWordAttaching w hw).comp
    (⟨fun z : UnitBoundary (Fin 2 → ℝ) => ⟨j, z⟩, by
      exact continuous_sigmaMk («σ» := fun _ : J => UnitBoundary (Fin 2 → ℝ)) (i := j)⟩ :
        C(UnitBoundary (Fin 2 → ℝ), BoundaryFamily J (Fin 2 → ℝ)))

theorem squareLoopDesc_classicalPresReadTraversal :
    squareLoopDesc (classicalPresReadTraversal w j (List.length_pos_of_ne_nil (hw j))) =
      (classicalPresCellBoundary w j hw).comp unitBoundarySquareHomeomorph.symm.toContinuousMap := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, rfl⟩ := squareBoundaryTraversal_surjective z
  rw (config := { transparency := .default }) [squareLoopDesc_traversal]
  have hb := (relatorCircleCycle w j (List.length_pos_of_ne_nil (hw j))).boundaryHomeomorph_traversal t
  change relatorCircleBoundaryHomeomorph w j (List.length_pos_of_ne_nil (hw j))
    (relatorCircleTraversal w j (List.length_pos_of_ne_nil (hw j)) t) =
      unitBoundarySquareHomeomorph.symm (squareBoundaryTraversal t) at hb
  change orderRoseRealizationHomeomorph A
    (presCircleWordMap w j (relatorCircleTraversal w j (List.length_pos_of_ne_nil (hw j)) t)) =
      classicalPresWordAttaching w hw
        ⟨j, unitBoundarySquareHomeomorph.symm (squareBoundaryTraversal t)⟩
  rw (config := { transparency := .default }) [← hb]
  exact (classicalPresWordAttaching_link w hw j _).symm

/-- The actual canonical disk attaching map reads exactly its word,
up to endpoint-preserving reparametrization of the traversal. -/
theorem classicalPresWordAttaching_homotopic_read :
    (classicalPresCellBoundary w j hw).Homotopic
      ((squareLoopDesc (classicalRoseRead (w j))).comp unitBoundarySquareHomeomorph.toContinuousMap) := by
  have H := squareLoopDesc_homotopic
    (classicalPresReadTraversal_homotopic_word w j (List.length_pos_of_ne_nil (hw j)))
  rw (config := { transparency := .default }) [squareLoopDesc_classicalPresReadTraversal w j hw] at H
  have H' := H.comp (ContinuousMap.Homotopic.refl unitBoundarySquareHomeomorph.toContinuousMap)
  have he : ((classicalPresCellBoundary w j hw).comp
      unitBoundarySquareHomeomorph.symm.toContinuousMap).comp
        unitBoundarySquareHomeomorph.toContinuousMap = classicalPresCellBoundary w j hw := by
    apply ContinuousMap.ext
    intro z
    exact congrArg (classicalPresCellBoundary w j hw) (unitBoundarySquareHomeomorph.symm_apply_apply z)
  rwa [he] at H'

end FiniteChains.PresModel
