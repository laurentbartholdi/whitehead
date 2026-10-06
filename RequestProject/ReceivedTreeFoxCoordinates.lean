module

public import RequestProject.ReceivedTreeCover
public import RequestProject.FoxWordBoundary

@[expose] public section

/-! Fox coordinates of the actual cover over the receiving group. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
open scoped Classical
universe u
variable {G : Type u} [Group G]

/-- Read one cell coordinate while retaining its full group-ring coefficient. -/
noncomputable def cellCoefficient {E : Type u} (e : E) :
    ((G × E) →₀ ℤ) →ₗ[ℤ] MonoidAlgebra ℤ G := by
  classical
  exact Finsupp.linearCombination ℤ (fun x =>
    if x.2 = e then MonoidAlgebra.single x.1 1 else 0)

theorem cellCoefficient_single {E : Type u} (e : E) (g : G) (j : E) (n : ℤ) :
    cellCoefficient e (Finsupp.single (g, j) n) =
      if j = e then MonoidAlgebra.single g n else 0 := by
  classical
  rw [cellCoefficient, Finsupp.linearCombination_single]
  split_ifs <;> simp [MonoidAlgebra.smul_single]

theorem cellCoefficient_apply {E : Type u} (e : E) (c : (G × E) →₀ ℤ) (g : G) :
    (cellCoefficient e c).coeff g = c (g, e) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    rw [map_add]
    change (cellCoefficient e c).coeff g + (cellCoefficient e d).coeff g = c (g, e) + d (g, e)
    rw [hc, hd]
  | single x n =>
    obtain ⟨h, j⟩ := x
    rw [cellCoefficient_single]
    by_cases hj : j = e <;> by_cases hg : h = g <;> simp [hj, hg]

/-- Assemble arbitrary group-ring coefficients into the actual finite cell chain. -/
noncomputable def cellCoordinates (E : Type u) [Fintype E] :
    ((G × E) →₀ ℤ) ≃ₗ[ℤ] (E → MonoidAlgebra ℤ G) :=
  (Finsupp.domLCongr (Equiv.prodComm G E)).trans
    ((Finsupp.curryLinearEquiv (R := ℤ)).trans
      ((Finsupp.linearEquivFunOnFinite ℤ (G →₀ ℤ) E).trans
        (LinearEquiv.piCongrRight (fun _ => (MonoidAlgebra.coeffLinearEquiv ℤ).symm))))

omit [Group G] in
theorem cellCoordinates_apply (E : Type u) [Fintype E]
    (c : (G × E) →₀ ℤ) (e : E) (g : G) :
    (cellCoordinates E c e).coeff g = c (g, e) := by
  change ((Finsupp.equivMapDomain (Equiv.prodComm G E) c).curry e) g = c (g, e)
  rw [Finsupp.curry_apply, Finsupp.equivMapDomain_apply]
  rfl

theorem cellCoefficient_eq_coordinates (E : Type u) [Fintype E]
    (c : (G × E) →₀ ℤ) (e : E) :
    cellCoefficient e c = cellCoordinates E c e := by
  ext g
  rw [cellCoefficient_apply, cellCoordinates_apply]

theorem cellCoefficient_coordinates_symm (E : Type u) [Fintype E]
    (v : E → MonoidAlgebra ℤ G) (e : E) :
    cellCoefficient e ((cellCoordinates E).symm v) = v e := by
  rw [cellCoefficient_eq_coordinates, LinearEquiv.apply_symm_apply]

variable {K : Complex2.{u}} (T : SpanningTree K)
  (φ : PresGroup (treeRel T) →* G)

noncomputable def coefficientMap : FreeGroupRing (NonTree T) →+* MonoidAlgebra ℤ G :=
  (MonoidAlgebra.mapDomainRingHom ℤ φ).comp (quotRingHom ℤ (relSub (treeRel T)))

theorem coefficientMap_grp (w : FreeGroup (NonTree T)) :
    coefficientMap T φ (grp w) = MonoidAlgebra.single (φ (QuotientGroup.mk w)) 1 := by
  change MonoidAlgebra.mapDomain φ
    (quotRingHom ℤ (relSub (treeRel T)) (MonoidAlgebra.single w 1)) = _
  rw [quotRingHom_single, MonoidAlgebra.mapDomain_single]

variable [DecidableEq (NonTree T)]

/-- The signed contribution of one genuinely lifted oriented edge. -/
theorem cellCoefficient_liftGerm (i : NonTree T) (g : G) (e : K.E × Bool) :
    cellCoefficient (G := G) i.1 (pathChain [liftGerm T φ g e]) =
      MonoidAlgebra.single g 1 * coefficientMap T φ (fox i (germWord T e)) := by
  classical
  obtain ⟨e, b⟩ := e
  by_cases ht : T.isTree e
  · have hne : e ≠ i.1 := fun h => i.2 (h ▸ ht)
    cases b <;>
      simp [liftGerm, germValue, germWord, ht, pathChain, cellCoefficient_single, hne]
  · by_cases hi : e = i.1
    · subst e
      cases b <;>
        simp [liftGerm, germValue, germWord, ht, pathChain, cellCoefficient_single,
          fox_inv, coefficientMap_grp, MonoidAlgebra.single_mul_single]
    · have hni : i ≠ (⟨e, ht⟩ : NonTree T) := fun h => hi (congrArg Subtype.val h).symm
      cases b <;>
        simp [liftGerm, germValue, germWord, ht, pathChain, cellCoefficient_single,
          fox_inv, hni, hi]

/-- The whole lifted marked path has the translated Fox coefficient of its
actual tree word. No quotient of G or augmentation is taken. -/
theorem cellCoefficient_liftPath (i : NonTree T) (g : G) (p : List (K.E × Bool)) :
    cellCoefficient (G := G) i.1 (pathChain (liftPath T φ p g)) =
      MonoidAlgebra.single g 1 * coefficientMap T φ (fox i (pathWord T p)) := by
  induction p generalizing g with
  | nil => simp
  | cons e p ih =>
    rw [liftPath_cons]
    have hc : pathChain (liftGerm T φ g e :: liftPath T φ p (g * germValue T φ e)) =
        pathChain [liftGerm T φ g e] + pathChain (liftPath T φ p (g * germValue T φ e)) :=
      by simp [pathChain]
    rw [hc, map_add, cellCoefficient_liftGerm, ih, pathWord_cons, fox_mul,
      map_add, map_mul, coefficientMap_grp, mul_add, ← mul_assoc,
      MonoidAlgebra.single_mul_single, mul_one]
    rfl

variable [Fintype K.F]

/-- The actual cellular two-boundary has exactly the received Fox coordinates. -/
theorem cellCoefficient_bdry2 (i : NonTree T) (c : (G × K.F) →₀ ℤ) :
    cellCoefficient (G := G) i.1 (bdry2 (cover T φ) c) =
      ∑ t : K.F, cellCoefficient t c * coefficientMap T φ (fox i (treeRel T t)) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [map_add, hc, hd, add_mul, Finset.sum_add_distrib]
  | single x n =>
    obtain ⟨g, t⟩ := x
    rw [bdry2_single, map_smul]
    change n • cellCoefficient (G := G) i.1 (pathChain (liftPath T φ (K.att t) g)) = _
    rw [cellCoefficient_liftPath]
    rw [← smul_mul_assoc, MonoidAlgebra.smul_single]
    simp [cellCoefficient_single, treeRel]

end FiniteChains.Comb.ReceivedTree
