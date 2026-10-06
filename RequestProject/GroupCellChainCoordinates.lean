import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
universe u v
variable {G : Type u} {I : Type v}

/-- Integer coefficients on group/cell pairs are the corresponding group-ring cell coefficients. -/
noncomputable def groupCellChainEquiv :
    (G × I →₀ ℤ) ≃ₗ[ℤ] (I →₀ MonoidAlgebra ℤ G) :=
  ((Finsupp.domLCongr (R := ℤ) (M := ℤ) (Equiv.prodComm G I)).trans
    (Finsupp.curryLinearEquiv ℤ)).trans
    (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv (S := ℤ) (M := G) ℤ).symm)

/-- Actual individual incidences keep their group coefficient and cell label under reindexing. -/
theorem groupCellChainEquiv_single (g : G) (i : I) (n : ℤ) :
    groupCellChainEquiv (Finsupp.single (g, i) n) =
      Finsupp.single i (MonoidAlgebra.single g n) := by
  simp only [groupCellChainEquiv, LinearEquiv.trans_apply, Finsupp.domLCongr_single,
    Finsupp.mapRange.linearEquiv_apply]
  change Finsupp.mapRange _ _ (Finsupp.single (i, g) n).curry = _
  rw [Finsupp.curry_single (i, g) n]
  simp [Finsupp.mapRange_single, MonoidAlgebra.coeffLinearEquiv_symm_apply]

/-- Left translation of actual group/cell incidences becomes group-ring scalar multiplication. -/
theorem groupCellChainEquiv_left_translate [Group G] (g : G) (c : G × I →₀ ℤ) :
    groupCellChainEquiv (Finsupp.mapDomain (fun q : G × I => (g * q.1, q.2)) c) =
      MonoidAlgebra.single g (1 : ℤ) • groupCellChainEquiv c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [Finsupp.mapDomain_add, map_add, hc, hd, smul_add]
  | single q n =>
    rw [Finsupp.mapDomain_single, groupCellChainEquiv_single, groupCellChainEquiv_single,
      Finsupp.smul_single]
    congr 1
    change MonoidAlgebra.single (g * q.1) n = MonoidAlgebra.single g 1 * MonoidAlgebra.single q.1 n
    simp only [MonoidAlgebra.single_mul_single, one_mul]

end FiniteChains
