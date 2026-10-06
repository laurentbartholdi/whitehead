module

public import RequestProject.FinitePosetCycleRealization
public import RequestProject.OrderNerveRealizationMapCoordinates

@[expose] public section

/-! The explicit cycle boundary parametrization is natural under a map
preserving the ordered vertex enumeration. Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval
open Set Topology

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.RelativeAttachment

theorem arcConcat_natural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (n : ℕ) (v : Fin (n + 2) → X) (w : Fin (n + 2) → Y)
    (F : ∀ i : Fin (n + 1), Path (v i.castSucc) (v i.succ))
    (G : ∀ i : Fin (n + 1), Path (w i.castSucc) (w i.succ))
    (h : ∀ i t, f (F i t) = G i t) (t : I) :
    f (arcConcat n v F t) = arcConcat n w G t := by
  induction n generalizing t with
  | zero => exact h 0 t
  | succ n ih =>
    simp only [arcConcat, Path.trans_apply]
    split_ifs
    · exact ih (v ∘ Fin.castSucc) (w ∘ Fin.castSucc)
        (fun i => F i.castSucc) (fun i => G i.castSucc)
        (fun i s => h i.castSucc s) _
    · exact h (Fin.last (n + 1)) _

end FiniteChains.RelativeAttachment

namespace FiniteChains.Comb
open RelativeAttachment

theorem orderNerveComparablePath_natural_bijective {P Q : Type}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) (hf : Monotone f)
    (hb : Function.Bijective f) {a b : P} (h : a ≤ b ∨ b ≤ a)
    (h' : f a ≤ f b ∨ f b ≤ f a) (t : I) :
    orderNerveRealizationMap f hf (orderNerveComparablePath h t) =
      orderNerveComparablePath h' t := by
  apply orderNerveRealizationCoordinates_injective Q
  funext q
  obtain ⟨p, rfl⟩ := hb.2 q
  rw [orderNerveRealizationCoordinates_map_injective f hf hb.1]
  simp only [orderNerveComparablePath_coordinates, hb.1.eq_iff]

namespace FinitePosetCycle

variable {P Q : Type} [PartialOrder P] [PartialOrder Q] {n : ℕ}
  (C : FinitePosetCycle P n) (D : FinitePosetCycle Q n)
  (f : P → Q) (hf : Monotone f) (hv : ∀ i, f (C.vertex i) = D.vertex i)

include hv in
theorem vertex_map_bijective : Function.Bijective f := by
  constructor
  · intro a b hab
    obtain ⟨i, rfl⟩ := C.vertex.surjective a
    obtain ⟨j, rfl⟩ := C.vertex.surjective b
    rw [hv, hv] at hab
    exact congrArg C.vertex (D.vertex.injective hab)
  · intro q
    obtain ⟨i, rfl⟩ := D.vertex.surjective q
    exact ⟨C.vertex i, hv i⟩

include hv in
theorem edge_natural (i : Fin (n + 1)) (t : I) :
    orderNerveRealizationMap f hf (C.edge i t) = D.edge i t := by
  have h' : f (C.vertex i.castSucc) ≤ f (C.vertex i.succ) ∨
      f (C.vertex i.succ) ≤ f (C.vertex i.castSucc) :=
    (C.consecutive i).imp (fun h => hf h) (fun h => hf h)
  have h := orderNerveComparablePath_natural_bijective f hf
    (C.vertex_map_bijective D f hv) (C.consecutive i) h' t
  apply h.trans
  apply orderNerveRealizationCoordinates_injective Q
  funext q
  simp only [edge, orderNerveComparablePath_coordinates, hv]

include hv in
theorem lastEdge_natural (t : I) :
    orderNerveRealizationMap f hf (C.lastEdge t) = D.lastEdge t := by
  have h' : f (C.vertex (Fin.last (n + 1))) ≤ f (C.vertex 0) ∨
      f (C.vertex 0) ≤ f (C.vertex (Fin.last (n + 1))) :=
    C.closing.imp (fun h => hf h) (fun h => hf h)
  have h := orderNerveComparablePath_natural_bijective f hf
    (C.vertex_map_bijective D f hv) C.closing h' t
  apply h.trans
  apply orderNerveRealizationCoordinates_injective Q
  funext q
  simp only [lastEdge, orderNerveComparablePath_coordinates, hv]

include hv in
theorem traversal_natural (t : I) :
    orderNerveRealizationMap f hf (C.traversal t) = D.traversal t := by
  have hp := arcConcat_natural (orderNerveRealizationMap f hf) n
    (orderNerveRealizationVertex ∘ C.vertex) (orderNerveRealizationVertex ∘ D.vertex)
    C.edge D.edge (C.edge_natural D f hf hv)
  simp only [traversal, Path.trans_apply]
  split_ifs
  · exact hp _
  · exact C.lastEdge_natural D f hf hv _

theorem boundaryHomeomorph_traversal (t : I) :
    C.boundaryHomeomorph (C.traversal t) =
      unitBoundarySquareHomeomorph.symm (squareBoundaryTraversal t) := by
  apply C.boundaryHomeomorph.symm.injective
  rw [Homeomorph.symm_apply_apply]
  change C.traversal t = simpleLoopBoundaryHomeomorph C.traversal
    C.traversal_surjective C.traversal_fiber
      (unitBoundarySquareHomeomorph.symm (squareBoundaryTraversal t))
  simp only [simpleLoopBoundaryHomeomorph, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply, simpleLoopSquareHomeomorph_traversal]

include hv in
theorem boundaryHomeomorph_natural (x : orderNerveRealization P) :
    D.boundaryHomeomorph (orderNerveRealizationMap f hf x) = C.boundaryHomeomorph x := by
  obtain ⟨t, rfl⟩ := C.traversal_surjective x
  rw [C.traversal_natural D f hf hv, D.boundaryHomeomorph_traversal,
    C.boundaryHomeomorph_traversal]

theorem boundaryHomeomorph_natural_cast {m : ℕ} (D' : FinitePosetCycle Q m)
    (hnm : n = m) (f' : P → Q) (hf' : Monotone f')
    (hv' : ∀ i, f' (C.vertex i) = D'.vertex (Fin.cast (congrArg (fun k => k + 2) hnm) i))
    (x : orderNerveRealization P) :
    D'.boundaryHomeomorph (orderNerveRealizationMap f' hf' x) = C.boundaryHomeomorph x := by
  subst m
  exact C.boundaryHomeomorph_natural D' f' hf' hv' x

end FinitePosetCycle
end FiniteChains.Comb
