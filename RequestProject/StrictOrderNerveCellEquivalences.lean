import RequestProject.MathlibOrderNerveCells
import RequestProject.StrictOrderComplex

/-! Literal identification of strict combinatorial vertices, edges and
triangles with the nondegenerate cells of the actual poset nerve. Pending
final Lean verification. -/

namespace FiniteChains.Comb
open CategoryTheory
universe u
variable (P : Type u) [PartialOrder P]

def vertexNerveEquiv : P ≃ (nerve P).nonDegenerate 0 where
  toFun p := ⟨ComposableArrows.mk₀ p,
    (PartialOrder.mem_nerve_nonDegenerate_iff_injective _).mpr
      (fun i j _ => @Subsingleton.elim (Fin 1) inferInstance i j)⟩
  invFun s := s.val.obj 0
  left_inv _ := rfl
  right_inv s := by
    apply Subtype.ext
    exact ComposableArrows.ext₀ rfl

def strictEdgeNerveEquiv : StrictOrdEdge P ≃ (nerve P).nonDegenerate 1 where
  toFun e := ⟨ordEdgeNerveEquiv P ⟨e.val, e.property.le⟩, by
    apply (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).mpr
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [Fin.lt_def] at hij
    exact e.property⟩
  invFun s := ⟨(s.val.obj 0, s.val.obj 1),
    ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).mp s.property) (by decide)⟩
  left_inv e := Subtype.ext rfl
  right_inv s := by
    apply Subtype.ext
    change ordEdgeNerveEquiv P ((ordEdgeNerveEquiv P).symm s.val) = s.val
    exact (ordEdgeNerveEquiv P).apply_symm_apply s.val

def strictTriNerveEquiv : StrictOrdTri P ≃ (nerve P).nonDegenerate 2 where
  toFun t := ⟨ordTriNerveEquiv P ⟨t.val, t.property.1.le, t.property.2.le⟩, by
    apply (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).mpr
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [Fin.lt_def] at hij
    all_goals first | exact t.property.1 | exact t.property.2 |
      exact t.property.1.trans t.property.2⟩
  invFun s := ⟨(s.val.obj 0, s.val.obj 1, s.val.obj 2),
    ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).mp s.property) (by decide),
    ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).mp s.property) (by decide)⟩
  left_inv t := Subtype.ext rfl
  right_inv s := by
    apply Subtype.ext
    change ordTriNerveEquiv P ((ordTriNerveEquiv P).symm s.val) = s.val
    exact (ordTriNerveEquiv P).apply_symm_apply s.val

end FiniteChains.Comb
