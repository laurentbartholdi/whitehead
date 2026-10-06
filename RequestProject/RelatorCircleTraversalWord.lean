import RequestProject.RelatorCircleIndexedWord
import RequestProject.OrderNerveAffinePathWords
import RequestProject.FinitePosetCycleNaturality

/-! The explicit once-around circle traversal represents its literal
four-edges-per-letter word as an actual based path homotopy.
Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval Topology
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb RelativeAttachment ContinuousEdgeWords

variable {A J : Type} (w : J → List (A × Bool)) (j : J) (hn : 0 < (w j).length)

def circleWordVertex (i : Fin (relatorCircleSize w j + 2)) : TCirc w :=
  (relatorCircleEnumeration w j hn i).val

def circleWordGerm (i : Fin (relatorCircleSize w j + 2)) : (orderCx (TCirc w)).E × Bool :=
  circleIndexedGerm w j (Fin.cast (relatorCircleSize_add_two w j hn) i)

theorem circleWordGerm_src (i : Fin (relatorCircleSize w j + 2)) :
    circleWordVertex w j hn i =
      germSrc (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt (circleWordGerm w j hn i) := by
  rw [circleWordGerm, circleIndexedGerm_src]
  rfl

theorem circleWordGerm_tgt (i : Fin (relatorCircleSize w j + 1)) :
    germTgt (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt
      (circleWordGerm w j hn i.castSucc) = circleWordVertex w j hn i.succ := by
  rw [circleWordGerm, circleIndexedGerm_tgt w j hn]
  exact congrArg Subtype.val (relatorCircleEnumeration_next w j hn i)

theorem circleWordGerm_last_tgt :
    germTgt (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt
      (circleWordGerm w j hn (Fin.last (relatorCircleSize w j + 1))) =
        circleWordVertex w j hn 0 := by
  rw [circleWordGerm, circleIndexedGerm_tgt w j hn]
  exact congrArg Subtype.val (relatorCircleEnumeration_last_next w j hn)

theorem circleWordGerms_eq : List.ofFn (circleWordGerm w j hn) = circLoop w j := by
  rw [List.ofFn_congr (relatorCircleSize_add_two w j hn)]
  have he : (fun i => circleWordGerm w j hn
      (Fin.cast (relatorCircleSize_add_two w j hn).symm i)) = circleIndexedGerm w j := by
    funext i
    rfl
  rw [he, circleIndexedGerm_ofFn]

def circleWordEdge (i : Fin (relatorCircleSize w j + 1)) :
    Path (orderNerveRealizationVertex (circleWordVertex w j hn i.castSucc))
      (orderNerveRealizationVertex (circleWordVertex w j hn i.succ)) :=
  orderNerveComparablePath (P := TCirc w) ((relatorCircleCycle w j hn).consecutive i)

def circleWordLastEdge :
    Path (orderNerveRealizationVertex
      (circleWordVertex w j hn (Fin.last (relatorCircleSize w j + 1))))
        (orderNerveRealizationVertex (circleWordVertex w j hn 0)) :=
  orderNerveComparablePath (P := TCirc w) (relatorCircleCycle w j hn).closing

def circleFullLoop :
    Path (orderNerveRealizationVertex (circleWordVertex w j hn 0))
      (orderNerveRealizationVertex (circleWordVertex w j hn 0)) :=
  (arcConcat (relatorCircleSize w j)
    (orderNerveRealizationVertex ∘ circleWordVertex w j hn) (circleWordEdge w j hn)).trans
      (circleWordLastEdge w j hn)

theorem circleTraversal_to_full (t : I) :
    orderNerveRealizationMap (Subtype.val : RelatorCircle w j → TCirc w) (fun _ _ h => h)
      (relatorCircleTraversal w j hn t) = circleFullLoop w j hn t := by
  have he (i : Fin (relatorCircleSize w j + 1)) (s : I) :
      orderNerveRealizationMap (Subtype.val : RelatorCircle w j → TCirc w) (fun _ _ h => h)
        ((relatorCircleCycle w j hn).edge i s) = circleWordEdge w j hn i s :=
    orderNerveComparablePath_natural Subtype.val (fun _ _ h => h)
      ((relatorCircleCycle w j hn).consecutive i)
      ((relatorCircleCycle w j hn).consecutive i) s
  have hp := arcConcat_natural
    (orderNerveRealizationMap (Subtype.val : RelatorCircle w j → TCirc w) (fun _ _ h => h))
    (relatorCircleSize w j)
    (orderNerveRealizationVertex ∘ (relatorCircleCycle w j hn).vertex)
    (orderNerveRealizationVertex ∘ circleWordVertex w j hn)
    (relatorCircleCycle w j hn).edge (circleWordEdge w j hn) he
  change orderNerveRealizationMap Subtype.val (fun _ _ h => h)
    (((relatorCircleCycle w j hn).prefix.trans (relatorCircleCycle w j hn).lastEdge) t) = _
  simp only [circleFullLoop, Path.trans_apply]
  split_ifs
  · exact hp _
  · exact orderNerveComparablePath_natural Subtype.val (fun _ _ h => h)
      (relatorCircleCycle w j hn).closing (relatorCircleCycle w j hn).closing _

def circleWordIndexedValid :
    IsPath (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt
      (List.ofFn (circleWordGerm w j hn)) (circleWordVertex w j hn 0) (circleWordVertex w j hn 0) := by
  rw [List.ofFn_succ', List.concat_eq_append]
  exact (isPath_ofFn _ _ (relatorCircleSize w j + 1) (circleWordVertex w j hn)
    (fun i => circleWordGerm w j hn i.castSucc)
    (fun i => circleWordGerm_src w j hn i.castSucc) (circleWordGerm_tgt w j hn)).append
    ⟨circleWordGerm_src w j hn _, circleWordGerm_last_tgt w j hn⟩

def circleWordValid : IsPath (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt
    (circLoop w j) (circleWordVertex w j hn 0) (circleWordVertex w j hn 0) := by
  rw [← circleWordGerms_eq w j hn]
  exact circleWordIndexedValid w j hn

theorem circleFullLoop_homotopic_word :
    (circleFullLoop w j hn).Homotopic
      (affineOrderWordPath (circLoop w j) (circleWordValid w j hn)) := by
  have hp := (arcConcat_homotopic_concat (relatorCircleSize w j)
      (orderNerveRealizationVertex ∘ circleWordVertex w j hn) (circleWordEdge w j hn)).trans
    (concat_homotopic_realize_ofFn (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt
      (orderNerveRealizationVertex (P := TCirc w))
      (fun e => orderNerveAffineEdgePath (P := TCirc w) e.property)
      (relatorCircleSize w j + 1) (circleWordVertex w j hn)
      (fun i => circleWordGerm w j hn i.castSucc)
      (fun i => circleWordGerm_src w j hn i.castSucc) (circleWordGerm_tgt w j hn)
      (circleWordEdge w j hn) (fun i => comparablePath_homotopic_single (P := TCirc w)
        ((relatorCircleCycle w j hn).consecutive i) _
        (circleWordGerm_src w j hn i.castSucc) (circleWordGerm_tgt w j hn i)))
  have hl := comparablePath_homotopic_single (P := TCirc w) (relatorCircleCycle w j hn).closing
    (circleWordGerm w j hn (Fin.last (relatorCircleSize w j + 1)))
    (circleWordGerm_src w j hn _) (circleWordGerm_last_tgt w j hn)
  have H := (hp.hcomp hl).trans
    (realize_append (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt
      (orderNerveRealizationVertex (P := TCirc w))
      (fun e => orderNerveAffineEdgePath (P := TCirc w) e.property)
      (List.ofFn (fun i : Fin (relatorCircleSize w j + 1) => circleWordGerm w j hn i.castSucc))
      [circleWordGerm w j hn (Fin.last (relatorCircleSize w j + 1))]
      (isPath_ofFn _ _ (relatorCircleSize w j + 1) (circleWordVertex w j hn)
        (fun i => circleWordGerm w j hn i.castSucc)
        (fun i => circleWordGerm_src w j hn i.castSucc) (circleWordGerm_tgt w j hn))
      ⟨circleWordGerm_src w j hn _, circleWordGerm_last_tgt w j hn⟩)
  have hw : List.ofFn (fun i => circleWordGerm w j hn i.castSucc) ++
      [circleWordGerm w j hn (Fin.last (relatorCircleSize w j + 1))] = circLoop w j := by
    rw [← List.concat_eq_append, ← List.ofFn_succ', circleWordGerms_eq]
  simpa only [hw, circleFullLoop, circleWordLastEdge, relatorCircleCycle, affineOrderWordPath, Function.comp_apply] using H

end FiniteChains.PresModel
