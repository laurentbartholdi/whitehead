import RequestProject.PresUniversalGroupRingBoundary
import RequestProject.CoverFoxTranslatedPrefixSum
import RequestProject.FoxFinsupp

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} [DecidableEq α] (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

/-- The genuine geometric boundary coefficient is the actual translated projected Fox derivative. -/
theorem presUniversalGroupRingBoundary_actual_fox
    (p : PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w))) (i : α) :
    presUniversalGroupRingBoundary ρ w hw hpos
      (Finsupp.single p.val.2 (MonoidAlgebra.single
        ((presGroupCocycle ρ w hw).readVertex (ptBase w) p.val.1) 1)) i =
      MonoidAlgebra.single ((presGroupCocycle ρ w hw).readVertex (ptBase w) p.val.1) 1 *
        proj (relSub ρ) (fox i (ρ p.val.2)) := by
  classical
  rw [presUniversalGroupRingBoundary_actual_column, ← hw p.val.2,
    coverFox_translated_prefix_sum]
  rw [Finsupp.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finsupp.smul_apply]
  by_cases hi : i = ((w p.val.2)[k.val]).1
  · subst i
    simp only [Finsupp.single_eq_same]
    cases hb : ((w p.val.2)[k.val]).2 <;>
      simp
  · simp [hi]

/-- Every group-translated geometric basis column is the corresponding Fox column. -/
theorem presUniversalGroupRingBoundary_fox_single (g : PresGroup ρ) (j : J) (i : α) :
    presUniversalGroupRingBoundary ρ w hw hpos
      (Finsupp.single j (MonoidAlgebra.single g 1)) i =
      MonoidAlgebra.single g 1 * proj (relSub ρ) (fox i (ρ j)) := by
  let p := (presUniversalRelatorGroupEquiv ρ w hw hpos).symm (g, j)
  have he := (presUniversalRelatorGroupEquiv ρ w hw hpos).apply_symm_apply (g, j)
  have hg : (presGroupCocycle ρ w hw).readVertex (ptBase w) p.val.1 = g :=
    congrArg Prod.fst he
  have hj : p.val.2 = j := congrArg Prod.snd he
  simpa only [hg, hj] using presUniversalGroupRingBoundary_actual_fox ρ w hw hpos p i

/-- The genuine universal geometric boundary equals the actual algebraic Fox boundary. -/
theorem presUniversalGroupRingBoundary_eq_fox :
    presUniversalGroupRingBoundary ρ w hw hpos =
      (coverSecondBoundary (relSub ρ) ρ).restrictScalars ℤ := by
  apply Finsupp.lhom_ext
  intro j r
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add r s hr hs => simp only [Finsupp.single_add, map_add, hr, hs]
  | single g n =>
    have hn : MonoidAlgebra.single g n = n • MonoidAlgebra.single g (1 : ℤ) := by
      simp [MonoidAlgebra.smul_single]
    change presUniversalGroupRingBoundary ρ w hw hpos
      (Finsupp.single j (MonoidAlgebra.single g n)) =
      (coverSecondBoundary (relSub ρ) ρ).restrictScalars ℤ
        (Finsupp.single j (MonoidAlgebra.single g n))
    rw [hn, ← Finsupp.smul_single, map_smul, map_smul]
    congr 1
    ext i
    rw [presUniversalGroupRingBoundary_fox_single]
    simp [coverSecondBoundary, coverFoxGradient, foxGradient_apply,
      Finsupp.linearCombination_single, Finsupp.smul_apply, smul_eq_mul]

end FiniteChains.PresModel
