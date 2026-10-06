import RequestProject.ChamberQuotientCover
import RequestProject.OrderPosetCoverThree

/-! The full Davis nerve covers the quotient cube poset, including its three-cells. -/

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

omit [Fintype V] in
theorem qProjCube_monotone : Monotone (qProjCube (A := A)) := by
  intro p q h
  refine ⟨h.1, fun w hw => ?_⟩
  have hwp : w ∉ p.spx := fun hc => hw (h.1 hc)
  rw [qProjCube_sgn_of_not_mem hwp, qProjCube_sgn_of_not_mem hw]
  exact (phi_rep_eq_of_inChamber (inChamber_rep_of_le h) hw).symm

/-- The actual quotient projection is a poset covering, before removing any chambers. -/
theorem qProjCube_isPosetCover : IsPosetCover (qProjCube (A := A)) where
  mono := qProjCube_monotone
  surj c := exists_zOld_qProjCube c
  up _ _ h := existsUnique_up_old h
  down _ _ h := existsUnique_down_old h

/-- The two-skeleton covering is constructed from the cube quotient. -/
theorem isCovering_orderCxMap_qProjCube :
    IsCovering (orderCxMap (qProjCube (A := A)) qProjCube_monotone) :=
  isCovering_orderCxMap qProjCube_isPosetCover

/-- Every three-simplex of the quotient lifts uniquely from any prescribed base lift. -/
theorem existsUnique_qProjCube_tetLift (s : OrdTet (QCube A)) (a : Sph A)
    (ha : qProjCube a = s.1.1) :
    ∃! t : OrdTet (Sph A), t.1.1 = a ∧
      ordTetMap (qProjCube (A := A)) qProjCube_monotone t = s :=
  qProjCube_isPosetCover.existsUnique_tetLift s a ha

end FiniteChains.Davis
