module

public import RequestProject.GenerationStep
public import RequestProject.CockcroftExtStep

@[expose] public section

/-! Relabelling the actual relators preserves Cockcroftness. All group,
coefficient, cycle and augmentation maps are constructed from the relator
equivalence and its literal word equality. Pending Lean verification. -/

noncomputable section
open scoped Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.RelatorReindex

universe u
variable {A J K : Type u} [Fintype A] [DecidableEq A] [Fintype J] [Fintype K]
  (ρ : J → FreeGroup A) (τ : K → FreeGroup A) (e : J ≃ K)
  (hrel : ∀ j, τ (e j) = ρ j)

/-- The generators are fixed; only the names of relators change. -/
def groupMap : PresGroup ρ →* PresGroup τ :=
  QuotientGroup.lift _ (QuotientGroup.mk' (relSub τ)) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.subset_normalClosure ⟨e j, hrel j⟩)

def coefficientMap : MonoidAlgebra ℤ (PresGroup ρ) →+* MonoidAlgebra ℤ (PresGroup τ) :=
  MonoidAlgebra.mapDomainRingHom ℤ (groupMap ρ τ e hrel)

omit [Fintype A] [DecidableEq A] [Fintype J] [Fintype K] in
theorem coefficientMap_quot (x : FreeGroupRing A) :
    coefficientMap ρ τ e hrel (quotRingHom ℤ (relSub ρ) x) =
      quotRingHom ℤ (relSub τ) x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single g n =>
      change MonoidAlgebra.mapDomain _ (MonoidAlgebra.mapDomain _ (MonoidAlgebra.single g n)) =
        MonoidAlgebra.mapDomain _ (MonoidAlgebra.single g n)
      simp only [MonoidAlgebra.mapDomain_single]
      rfl

omit [Fintype A] [Fintype J] [Fintype K] in
theorem coefficientMap_matrix (a : A) (j : J) :
    coefficientMap ρ τ e hrel (foxMatrixPres ρ a j) = foxMatrixPres τ a (e j) := by
  change coefficientMap ρ τ e hrel (quotRingHom ℤ (relSub ρ) (fox a (ρ j))) =
    quotRingHom ℤ (relSub τ) (fox a (τ (e j)))
  rw [coefficientMap_quot, hrel]

def cells (v : J → MonoidAlgebra ℤ (PresGroup ρ)) :
    K → MonoidAlgebra ℤ (PresGroup τ) :=
  fun k => coefficientMap ρ τ e hrel (v (e.symm k))

omit [Fintype A] in
theorem cells_cycle (v : J → MonoidAlgebra ℤ (PresGroup ρ)) (hv : IsFoxCycle ρ v) :
    IsFoxCycle τ (cells ρ τ e hrel v) := by
  intro a
  have h := congrArg (coefficientMap ρ τ e hrel) (hv a)
  simp only [map_sum, map_mul, map_zero, coefficientMap_matrix] at h
  rw [← e.sum_comp (fun k => cells ρ τ e hrel v k * foxMatrixPres τ a k)]
  simpa only [cells, Equiv.symm_apply_apply] using h

omit [Fintype A] [DecidableEq A] [Fintype J] [Fintype K] in
theorem cells_aug (v : J → MonoidAlgebra ℤ (PresGroup ρ)) (k : K) :
    augPres τ (cells ρ τ e hrel v k) = augPres ρ (v (e.symm k)) :=
  augQ_mapDomain (groupMap ρ τ e hrel) (v (e.symm k))

def mor : PresMor ρ τ where
  hom := groupMap ρ τ e hrel
  cells := cells ρ τ e hrel
  cells_add := by
    intro v w
    funext k
    exact map_add (coefficientMap ρ τ e hrel) _ _
  cells_smul := by
    intro a v
    funext k
    exact map_mul (coefficientMap ρ τ e hrel) _ _
  cells_cycle := cells_cycle ρ τ e hrel
  cells_aug := by
    intro v hv k
    rw [cells_aug]
    exact hv (e.symm k)

include hrel in
omit [Fintype A] in
/-- Reflect Cockcroftness along the actual reindexing map. Surjectivity of
the relator equivalence supplies every original cell coefficient. -/
theorem isCockcroft_of (hτ : IsCockcroft τ) : IsCockcroft ρ := by
  intro v hv j
  have h := hτ (cells ρ τ e hrel v) (cells_cycle ρ τ e hrel v hv) (e j)
  simpa only [cells_aug, Equiv.symm_apply_apply] using h

include hrel in
omit [Fintype A] in
theorem isCockcroft_iff : IsCockcroft ρ ↔ IsCockcroft τ := by
  constructor
  · intro hρ
    have hs : ∀ k, ρ (e.symm k) = τ k := by
      intro k
      simpa only [Equiv.apply_symm_apply] using (hrel (e.symm k)).symm
    exact isCockcroft_of τ ρ e.symm hs hρ
  · exact isCockcroft_of ρ τ e hrel

end FiniteChains.RelatorReindex
