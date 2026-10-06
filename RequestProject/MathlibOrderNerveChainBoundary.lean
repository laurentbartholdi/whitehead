import RequestProject.MathlibOrderNerveCells
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory
variable (P : Type) [PartialOrder P]

/-- Mathlib's free integral module simplicial object of the actual poset nerve. -/
noncomputable def mathlibOrderNerveModule : SimplicialObject (ModuleCat ℤ) :=
  nerve P ⋙ ModuleCat.free ℤ

/-- The actual Mathlib alternating-face differential on a triangle agrees with
its actual cellular second boundary in order coordinates. -/
theorem mathlibOrderNerve_d2_single (t : OrdTri P) :
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 1).hom
      (Finsupp.single (ordTriNerveEquiv P t) 1) =
        Finsupp.mapDomain (ordEdgeNerveEquiv P)
          (bdry2 (orderCx P) (Finsupp.single t 1)) := by
  rw [ordTriangleBoundary_nerve_faces]
  simp [AlgebraicTopology.AlternatingFaceMapComplex.objD, mathlibOrderNerveModule,
    SimplicialObject.δ, Fin.sum_univ_succ, ModuleCat.free]
  abel

/-- The actual Mathlib alternating-face differential on a tetrahedron agrees
with its genuine order-nerve third boundary. -/
theorem mathlibOrderNerve_d3_single (t : OrdTet P) :
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 2).hom
      (Finsupp.single (ordTetNerveEquiv P t) 1) =
        Finsupp.mapDomain (ordTriNerveEquiv P) (ordTetBoundary t) := by
  rw [ordTetBoundary_nerve_faces]
  simp [AlgebraicTopology.AlternatingFaceMapComplex.objD, mathlibOrderNerveModule,
    SimplicialObject.δ, Fin.sum_univ_succ, ModuleCat.free]
  abel

/-- Actual finite two-chains satisfy the Mathlib/cellular boundary comparison. -/
theorem mathlibOrderNerve_d2 (c : OrdTri P →₀ ℤ) :
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 1).hom
      (Finsupp.mapDomain (ordTriNerveEquiv P) c) =
        Finsupp.mapDomain (ordEdgeNerveEquiv P) (bdry2 (orderCx P) c) := by
  change ((AlgebraicTopology.AlternatingFaceMapComplex.objD
    (mathlibOrderNerveModule P) 1).hom.comp
      (Finsupp.lmapDomain ℤ ℤ (ordTriNerveEquiv P))) c =
    ((Finsupp.lmapDomain ℤ ℤ (ordEdgeNerveEquiv P)).comp (bdry2 (orderCx P))) c
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd]
  | single t n =>
    have hn : Finsupp.single t n = n • Finsupp.single t (1 : ℤ) := by simp
    rw [hn, map_smul, map_smul]
    congr 1
    change (AlgebraicTopology.AlternatingFaceMapComplex.objD
      (mathlibOrderNerveModule P) 1).hom
      (Finsupp.mapDomain (ordTriNerveEquiv P) (Finsupp.single t 1)) = _
    rw [Finsupp.mapDomain_single]
    exact mathlibOrderNerve_d2_single P t

/-- Actual finite three-chains satisfy the Mathlib/order-nerve boundary comparison. -/
theorem mathlibOrderNerve_d3 (c : OrdTet P →₀ ℤ) :
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 2).hom
      (Finsupp.mapDomain (ordTetNerveEquiv P) c) =
        Finsupp.mapDomain (ordTriNerveEquiv P) (ordBoundary3 c) := by
  change ((AlgebraicTopology.AlternatingFaceMapComplex.objD
    (mathlibOrderNerveModule P) 2).hom.comp
      (Finsupp.lmapDomain ℤ ℤ (ordTetNerveEquiv P))) c =
    ((Finsupp.lmapDomain ℤ ℤ (ordTriNerveEquiv P)).comp ordBoundary3) c
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd]
  | single t n =>
    have hn : Finsupp.single t n = n • Finsupp.single t (1 : ℤ) := by simp
    rw [hn, map_smul, map_smul]
    congr 1
    change _ = Finsupp.mapDomain (ordTriNerveEquiv P)
      (ordBoundary3 (Finsupp.single t 1))
    rw [ordBoundary3, Finsupp.linearCombination_single, one_smul]
    change (AlgebraicTopology.AlternatingFaceMapComplex.objD
      (mathlibOrderNerveModule P) 2).hom
      (Finsupp.mapDomain (ordTetNerveEquiv P) (Finsupp.single t 1)) = _
    rw [Finsupp.mapDomain_single]
    exact mathlibOrderNerve_d3_single P t

end FiniteChains.Comb
