module

public import RequestProject.OrderNormalizationHomotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory
universe u
variable (P : Type u) [PartialOrder P]

/-- The project's actual weak edges are precisely Mathlib poset-nerve one-simplices. -/
def ordEdgeNerveEquiv : OrdEdge P ≃ ComposableArrows P 1 where
  toFun e := ComposableArrows.mk₁ (homOfLE e.2)
  invFun s := ⟨(s.obj 0, s.obj 1), s.monotone (by decide : (0 : Fin 2) ≤ 1)⟩
  left_inv e := Subtype.ext rfl
  right_inv s := by
    apply CategoryTheory.Functor.ext (fun i => by fin_cases i <;> rfl)

/-- The project's actual weak triangles are precisely Mathlib poset-nerve two-simplices. -/
def ordTriNerveEquiv : OrdTri P ≃ ComposableArrows P 2 where
  toFun t := ComposableArrows.mk₂ (homOfLE t.2.1) (homOfLE t.2.2)
  invFun s := ⟨(s.obj 0, s.obj 1, s.obj 2),
    s.monotone (by decide : (0 : Fin 3) ≤ 1),
    s.monotone (by decide : (1 : Fin 3) ≤ 2)⟩
  left_inv t := Subtype.ext rfl
  right_inv s := ComposableArrows.ext₂ rfl rfl rfl
    (Subsingleton.elim _ _) (Subsingleton.elim _ _)

/-- The project's actual weak tetrahedra are precisely Mathlib poset-nerve three-simplices. -/
def ordTetNerveEquiv : OrdTet P ≃ ComposableArrows P 3 where
  toFun t := ComposableArrows.mk₃ (homOfLE t.2.1) (homOfLE t.2.2.1) (homOfLE t.2.2.2)
  invFun s := ⟨(s.obj 0, s.obj 1, s.obj 2, s.obj 3),
    s.monotone (by decide : (0 : Fin 4) ≤ 1),
    s.monotone (by decide : (1 : Fin 4) ≤ 2),
    s.monotone (by decide : (2 : Fin 4) ≤ 3)⟩
  left_inv t := Subtype.ext rfl
  right_inv s := by
    apply CategoryTheory.Functor.ext (fun i => by fin_cases i <;> rfl)

/-- The actual alternating tetrahedron boundary is Mathlib's four nerve faces. -/
theorem ordTetBoundary_nerve_faces (t : OrdTet P) :
    Finsupp.mapDomain (ordTriNerveEquiv P) (ordTetBoundary t) =
      Finsupp.single ((nerve P).δ (0 : Fin 4) (ordTetNerveEquiv P t)) 1 -
      Finsupp.single ((nerve P).δ (1 : Fin 4) (ordTetNerveEquiv P t)) 1 +
      Finsupp.single ((nerve P).δ (2 : Fin 4) (ordTetNerveEquiv P t)) 1 -
      Finsupp.single ((nerve P).δ (3 : Fin 4) (ordTetNerveEquiv P t)) 1 := by
  change (Finsupp.lmapDomain ℤ ℤ (ordTriNerveEquiv P)) (ordTetBoundary t) = _
  simp only [ordTetBoundary, map_sub, map_add, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]
  have h0 : ordTriNerveEquiv P
      ⟨(t.1.2.1, t.1.2.2.1, t.1.2.2.2), t.2.2⟩ =
      (nerve P).δ (0 : Fin 4) (ordTetNerveEquiv P t) := by
    apply CategoryTheory.Functor.ext (fun i => by fin_cases i <;> rfl)
  have h1 : ordTriNerveEquiv P
      ⟨(t.1.1, t.1.2.2.1, t.1.2.2.2), t.2.1.trans t.2.2.1, t.2.2.2⟩ =
      (nerve P).δ (1 : Fin 4) (ordTetNerveEquiv P t) := by
    apply CategoryTheory.Functor.ext (fun i => by fin_cases i <;> rfl)
  have h2 : ordTriNerveEquiv P
      ⟨(t.1.1, t.1.2.1, t.1.2.2.2), t.2.1, t.2.2.1.trans t.2.2.2⟩ =
      (nerve P).δ (2 : Fin 4) (ordTetNerveEquiv P t) := by
    apply CategoryTheory.Functor.ext (fun i => by fin_cases i <;> rfl)
  have h3 : ordTriNerveEquiv P
      ⟨(t.1.1, t.1.2.1, t.1.2.2.1), t.2.1, t.2.2.1⟩ =
      (nerve P).δ (3 : Fin 4) (ordTetNerveEquiv P t) := by
    apply CategoryTheory.Functor.ext (fun i => by fin_cases i <;> rfl)
  rw [h0, h1, h2, h3]

/-- The actual two-cell boundary agrees with Mathlib's alternating nerve faces. -/
theorem ordTriangleBoundary_nerve_faces (t : OrdTri P) :
    Finsupp.mapDomain (ordEdgeNerveEquiv P)
      (bdry2 (orderCx P) (Finsupp.single t 1)) =
      Finsupp.single ((nerve P).δ (0 : Fin 3) (ordTriNerveEquiv P t)) 1 -
      Finsupp.single ((nerve P).δ (1 : Fin 3) (ordTriNerveEquiv P t)) 1 +
      Finsupp.single ((nerve P).δ (2 : Fin 3) (ordTriNerveEquiv P t)) 1 := by
  have h0 : ordEdgeNerveEquiv P ⟨(t.1.2.1, t.1.2.2), t.2.2⟩ =
      (nerve P).δ (0 : Fin 3) (ordTriNerveEquiv P t) := by
    apply CategoryTheory.Functor.ext (fun i => by fin_cases i <;> rfl)
  have h1 : ordEdgeNerveEquiv P ⟨(t.1.1, t.1.2.2), t.2.1.trans t.2.2⟩ =
      (nerve P).δ (1 : Fin 3) (ordTriNerveEquiv P t) := by
    apply CategoryTheory.Functor.ext (fun i => by fin_cases i <;> rfl)
  have h2 : ordEdgeNerveEquiv P ⟨(t.1.1, t.1.2.1), t.2.1⟩ =
      (nerve P).δ (2 : Fin 3) (ordTriNerveEquiv P t) := by
    apply CategoryTheory.Functor.ext (fun i => by fin_cases i <;> rfl)
  have hb : bdry2 (orderCx P) (Finsupp.single t 1) =
      Finsupp.single (⟨(t.1.1, t.1.2.1), t.2.1⟩ : OrdEdge P) 1 +
      Finsupp.single (⟨(t.1.2.1, t.1.2.2), t.2.2⟩ : OrdEdge P) 1 -
      Finsupp.single (⟨(t.1.1, t.1.2.2), t.2.1.trans t.2.2⟩ : OrdEdge P) 1 := by
    simp [bdry2, orderCx, pathChain]
    abel
  change (Finsupp.lmapDomain ℤ ℤ (ordEdgeNerveEquiv P))
    (bdry2 (orderCx P) (Finsupp.single t 1)) = _
  rw [hb, map_sub, map_add]
  simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, h0, h1, h2]
  abel

end FiniteChains.Comb
