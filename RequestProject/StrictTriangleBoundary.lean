module

public import RequestProject.StrictOrderChains

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

def strictTriangleEdge01 (t : StrictOrdTri P) : StrictOrdEdge P := ⟨(t.1.1, t.1.2.1), t.2.1⟩
def strictTriangleEdge12 (t : StrictOrdTri P) : StrictOrdEdge P := ⟨(t.1.2.1, t.1.2.2), t.2.2⟩
def strictTriangleEdge02 (t : StrictOrdTri P) : StrictOrdEdge P :=
  ⟨(t.1.1, t.1.2.2), t.2.1.trans t.2.2⟩

/-- The genuine cellular boundary of a strict triangle, with its actual orientations. -/
theorem strictTriangle_bdry2_single (t : StrictOrdTri P) (n : ℤ) :
    bdry2 (strictOrderCx P) (Finsupp.single t n) =
      Finsupp.single (strictTriangleEdge01 t) n +
      Finsupp.single (strictTriangleEdge12 t) n -
      Finsupp.single (strictTriangleEdge02 t) n := by
  rw [bdry2_single]
  simp only [strictOrderCx, pathChain_cons, pathChain_nil, if_true, Bool.false_eq_true,
    if_false, add_zero]
  rw [smul_add, smul_add, smul_neg]
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [sub_eq_add_neg, add_assoc]
  rfl

end FiniteChains.Comb
