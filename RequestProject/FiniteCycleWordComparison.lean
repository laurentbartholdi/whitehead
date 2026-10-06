module

public import RequestProject.FinitePosetCycleNaturality
public import RequestProject.OrderNerveAffinePathWords

@[expose] public section

/-! A monotone image of an explicit cycle reads its ordered edge word by
an actual endpoint-preserving path homotopy. Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval Topology
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.FinitePosetCycle
open RelativeAttachment ContinuousEdgeWords

variable {P Q : Type} [PartialOrder P] [PartialOrder Q] {n : ℕ}
  (C : FinitePosetCycle P n) (f : P → Q) (hf : Monotone f)

def mappedEdge (i : Fin (n + 1)) :=
  orderNerveComparablePath ((C.consecutive i).imp (fun h => hf h) (fun h => hf h))

def mappedLastEdge := orderNerveComparablePath (C.closing.imp (fun h => hf h) (fun h => hf h))

def mappedLoop : Path (orderNerveRealizationVertex (f (C.vertex 0)))
    (orderNerveRealizationVertex (f (C.vertex 0))) :=
  (arcConcat n (fun i => orderNerveRealizationVertex (f (C.vertex i)))
    (C.mappedEdge f hf)).trans (C.mappedLastEdge f hf)

theorem mappedLoop_apply (t : I) :
    C.mappedLoop f hf t = orderNerveRealizationMap f hf (C.traversal t) := by
  have hp := arcConcat_natural (orderNerveRealizationMap f hf) n
    (orderNerveRealizationVertex ∘ C.vertex)
    (fun i => orderNerveRealizationVertex (f (C.vertex i))) C.edge (C.mappedEdge f hf)
    (fun i s => orderNerveComparablePath_natural f hf
      (C.consecutive i) ((C.consecutive i).imp (fun h => hf h) (fun h => hf h)) s)
  simp only [mappedLoop, traversal, Path.trans_apply]
  split_ifs
  · exact (hp _).symm
  · exact (orderNerveComparablePath_natural f hf C.closing
      (C.closing.imp (fun h => hf h) (fun h => hf h)) _).symm

variable (g : Fin (n + 2) → (orderCx Q).E × Bool)
  (hs : ∀ i, f (C.vertex i) = germSrc (orderCx Q).src (orderCx Q).tgt (g i))
  (ht : ∀ i : Fin (n + 1), germTgt (orderCx Q).src (orderCx Q).tgt (g i.castSucc) =
    f (C.vertex i.succ))
  (hclose : germTgt (orderCx Q).src (orderCx Q).tgt (g (Fin.last (n + 1))) = f (C.vertex 0))

def mappedWordValid : IsPath (orderCx Q).src (orderCx Q).tgt (List.ofFn g)
    (f (C.vertex 0)) (f (C.vertex 0)) := by
  rw [List.ofFn_succ', List.concat_eq_append]
  exact (isPath_ofFn _ _ (n + 1) (f ∘ C.vertex) (fun i => g i.castSucc)
    (fun i => hs i.castSucc) ht).append ⟨hs _, hclose⟩

theorem mappedLoop_homotopic_word :
    (C.mappedLoop f hf).Homotopic
      (affineOrderWordPath (List.ofFn g) (C.mappedWordValid f g hs ht hclose)) := by
  have hp := (arcConcat_homotopic_concat n
      (fun i => orderNerveRealizationVertex (f (C.vertex i))) (C.mappedEdge f hf)).trans
    (concat_homotopic_realize_ofFn (orderCx Q).src (orderCx Q).tgt
      (orderNerveRealizationVertex (P := Q)) (fun e => orderNerveAffineEdgePath (P := Q) e.property)
      (n + 1) (f ∘ C.vertex) (fun i => g i.castSucc) (fun i => hs i.castSucc) ht
      (C.mappedEdge f hf) (fun i => comparablePath_homotopic_single
        ((C.consecutive i).imp (fun h => hf h) (fun h => hf h)) _ (hs i.castSucc) (ht i)))
  have hl := comparablePath_homotopic_single
    (C.closing.imp (fun h => hf h) (fun h => hf h)) (g (Fin.last (n + 1)))
    (hs _) hclose
  have H := (hp.hcomp hl).trans
    (realize_append (orderCx Q).src (orderCx Q).tgt (orderNerveRealizationVertex (P := Q))
      (fun e => orderNerveAffineEdgePath (P := Q) e.property)
      (List.ofFn (fun i : Fin (n + 1) => g i.castSucc)) [g (Fin.last (n + 1))]
      (isPath_ofFn _ _ (n + 1) (f ∘ C.vertex) (fun i => g i.castSucc)
        (fun i => hs i.castSucc) ht) ⟨hs _, hclose⟩)
  have he : List.ofFn (fun i : Fin (n + 1) => g i.castSucc) ++ [g (Fin.last (n + 1))] =
      List.ofFn g := by simpa only [List.concat_eq_append] using (List.ofFn_succ' g).symm
  simpa only [he, mappedLoop, mappedLastEdge, affineOrderWordPath] using H

end FiniteChains.Comb.FinitePosetCycle
