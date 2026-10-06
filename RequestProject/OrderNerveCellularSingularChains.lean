module

public import RequestProject.OrderNerveExplicitSingularMap

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular

noncomputable def orderCellSingularChain1 {P : Type} [PartialOrder P] :
    (OrdEdge P →₀ ℤ) →ₗ[ℤ] Chain (orderNerveRealization P) 1 :=
  ((orderNerveExplicitSingularMap P).f 1).hom.comp
    (Finsupp.lmapDomain ℤ ℤ (ordEdgeNerveEquiv P))

noncomputable def orderCellSingularChain2 {P : Type} [PartialOrder P] :
    (OrdTri P →₀ ℤ) →ₗ[ℤ] Chain (orderNerveRealization P) 2 :=
  ((orderNerveExplicitSingularMap P).f 2).hom.comp
    (Finsupp.lmapDomain ℤ ℤ (ordTriNerveEquiv P))

noncomputable def orderCellSingularChain3 {P : Type} [PartialOrder P] :
    (OrdTet P →₀ ℤ) →ₗ[ℤ] Chain (orderNerveRealization P) 3 :=
  ((orderNerveExplicitSingularMap P).f 3).hom.comp
    (Finsupp.lmapDomain ℤ ℤ (ordTetNerveEquiv P))

theorem orderCellSingularChain1_single {P : Type} [PartialOrder P] (e : OrdEdge P) (r : ℤ) :
    orderCellSingularChain1 (Finsupp.single e r) =
      Finsupp.single (orderNerveSingularSimplex (ordEdgeNerveEquiv P e)) r := by
  change (orderNerveExplicitSingularMap P).f 1
    (Finsupp.mapDomain (ordEdgeNerveEquiv P) (Finsupp.single e r)) = _
  rw (config := { transparency := .default }) [Finsupp.mapDomain_single]
  exact orderNerveExplicitSingularMap_single _ _ _

theorem orderCellSingularChain2_single {P : Type} [PartialOrder P] (t : OrdTri P) (r : ℤ) :
    orderCellSingularChain2 (Finsupp.single t r) =
      Finsupp.single (orderNerveSingularSimplex (ordTriNerveEquiv P t)) r := by
  change (orderNerveExplicitSingularMap P).f 2
    (Finsupp.mapDomain (ordTriNerveEquiv P) (Finsupp.single t r)) = _
  rw (config := { transparency := .default }) [Finsupp.mapDomain_single]
  exact orderNerveExplicitSingularMap_single _ _ _

theorem orderCellSingularChain3_single {P : Type} [PartialOrder P] (t : OrdTet P) (r : ℤ) :
    orderCellSingularChain3 (Finsupp.single t r) =
      Finsupp.single (orderNerveSingularSimplex (ordTetNerveEquiv P t)) r := by
  change (orderNerveExplicitSingularMap P).f 3
    (Finsupp.mapDomain (ordTetNerveEquiv P) (Finsupp.single t r)) = _
  rw (config := { transparency := .default }) [Finsupp.mapDomain_single]
  exact orderNerveExplicitSingularMap_single _ _ _

/-- The canonical realized cellular two-chain has exactly its singular boundary. -/
theorem orderCellSingularChain2_boundary {P : Type} [PartialOrder P] (c : OrdTri P →₀ ℤ) :
    boundary 1 (orderCellSingularChain2 c) = orderCellSingularChain1 (bdry2 (orderCx P) c) := by
  have h := congrArg (fun f => f (Finsupp.mapDomain (ordTriNerveEquiv P) c))
    ((orderNerveExplicitSingularMap P).comm 2 1).symm
  rw (config := { transparency := .default }) [complex_d, AlternatingFaceMapComplex.obj_d_eq] at h
  change (orderNerveExplicitSingularMap P).f 1
      ((AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 1).hom
        (Finsupp.mapDomain (ordTriNerveEquiv P) c)) =
    boundary 1 (orderCellSingularChain2 c) at h
  rw (config := { transparency := .default }) [mathlibOrderNerve_d2] at h
  exact h.symm

/-- The same comparison respects genuine cellular three-boundaries. -/
theorem orderCellSingularChain3_boundary {P : Type} [PartialOrder P] (c : OrdTet P →₀ ℤ) :
    boundary 2 (orderCellSingularChain3 c) = orderCellSingularChain2 (ordBoundary3 c) := by
  have h := congrArg (fun f => f (Finsupp.mapDomain (ordTetNerveEquiv P) c))
    ((orderNerveExplicitSingularMap P).comm 3 2).symm
  rw (config := { transparency := .default }) [complex_d, AlternatingFaceMapComplex.obj_d_eq] at h
  change (orderNerveExplicitSingularMap P).f 2
      ((AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 2).hom
        (Finsupp.mapDomain (ordTetNerveEquiv P) c)) =
    boundary 2 (orderCellSingularChain3 c) at h
  rw (config := { transparency := .default }) [mathlibOrderNerve_d3] at h
  exact h.symm

theorem orderCellSingularChain2_cycle {P : Type} [PartialOrder P]
    (c : OrdTri P →₀ ℤ) (hc : bdry2 (orderCx P) c = 0) :
    boundary 1 (orderCellSingularChain2 c) = 0 := by
  rw (config := { transparency := .default }) [orderCellSingularChain2_boundary, hc, map_zero]

end FiniteChains.Comb
