import RequestProject.CoverComplex
import RequestProject.CombLoopWord
import RequestProject.UniversalPathGauge
import RequestProject.CellularHomotopyChain
import RequestProject.ZeroPi2Descent

/-! Exact Fox expansion for a word of actual lifted loops. This is an
identity of edge chains, not merely of homology classes. Unverified source. -/
noncomputable section
open scoped Classical
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {X : Complex2.{u}} {a : X.V} {I : Type u}
  (N : Subgroup (FreeGroup I)) [N.Normal]
  (p : I → Loop X a) (ψ : (FreeGroup I ⧸ N) →* Pi1 X a)
  (hψ : ∀ i, ψ (qof N i) = Pi1.mk (p i))

def loopCoefficientVertex (g : FreeGroup I ⧸ N) : UV X a :=
  deckV (ψ g) (UV.base X a)

theorem loopCoefficientVertex_end (g : FreeGroup I ⧸ N) :
    endV (loopCoefficientVertex N ψ g) = a := by
  rw [loopCoefficientVertex, endV_deckV, endV_base]

include hψ in
theorem extendList_loopCoefficientVertex (i : I) (g : FreeGroup I ⧸ N) :
    extendList (p i).1 (loopCoefficientVertex N ψ g) =
      loopCoefficientVertex N ψ (g * qof N i) := by
  rw [loopCoefficientVertex, extendList_deckV, ← deckV_loop_base, ← hψ,
    ← deckV_mul, ← map_mul]
  rfl

include hψ in
theorem extendList_rev_loopCoefficientVertex (i : I) (g : FreeGroup I ⧸ N) :
    extendList (revPath (p i).1) (loopCoefficientVertex N ψ g) =
      loopCoefficientVertex N ψ (g * (qof N i)⁻¹) := by
  rw [loopCoefficientVertex, extendList_deckV]
  rw [← deckV_loop_base (⟨revPath (p i).1, isPath_revPath (p i).2⟩ : Loop X a)]
  change deckV (ψ g) (deckV ((Pi1.mk (p i))⁻¹) (UV.base X a)) = _
  rw [← hψ, ← map_inv, ← deckV_mul, ← map_mul]
  rfl

include hψ in
theorem lifted_loop_reverse_chain (i : I) (g : FreeGroup I ⧸ N) :
    pathChain (uLiftPath (revPath (p i).1) (loopCoefficientVertex N ψ g)) =
      -pathChain (uLiftPath (p i).1 (loopCoefficientVertex N ψ (g * (qof N i)⁻¹))) := by
  have hp : IsPath X.src X.tgt (p i).1
      (endV (loopCoefficientVertex N ψ (g * (qof N i)⁻¹))) a := by
    rw [loopCoefficientVertex_end]
    exact (p i).2
  have hl := isPath_uLiftPath (p i).1 (loopCoefficientVertex N ψ (g * (qof N i)⁻¹)) a hp
  have hcancel : (g * (qof N i)⁻¹) * qof N i = g := by group
  rw [extendList_loopCoefficientVertex N p ψ hψ, hcancel] at hl
  have hr := eq_uLiftPath_of_isPath _ _ _ (isPath_revPath hl)
  have hproj : mapPath (univProj X a)
      (uLiftPath (p i).1 (loopCoefficientVertex N ψ (g * (qof N i)⁻¹))) = (p i).1 :=
    map_uLiftPath (p i).1 _ a hp
  rw [mapPath_revPath, hproj] at hr
  rw [← hr, pathChain_revPath]

def loopCoefficientChainMap : ((FreeGroup I ⧸ N) × I →₀ ℤ) →ₗ[ℤ] (UE X a →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x =>
    pathChain (uLiftPath (p x.2).1 (loopCoefficientVertex N ψ x.1)))

include hψ in
/-- Replace each formal generator edge by its actual lifted loop. Negative
letters contribute the reverse path at the preceding sheet, exactly as Fox
differentiation requires. -/
theorem loopCoefficientChainMap_liftPath (l : List (I × Bool)) (g : FreeGroup I ⧸ N) :
    loopCoefficientChainMap N p ψ (pathChain (liftPath (Nsub := N) l g)) =
      pathChain (uLiftPath (wordPath p l) (loopCoefficientVertex N ψ g)) := by
  induction l generalizing g with
  | nil => simp [wordPath_nil]
  | cons ib l ih =>
      obtain ⟨i, b⟩ := ib
      cases b with
      | true =>
          have hp : IsPath X.src X.tgt (p i).1 (endV (loopCoefficientVertex N ψ g)) a := by
            rw [loopCoefficientVertex_end]
            exact (p i).2
          rw [liftPath_cons_true, pathChain_cons, wordPath_cons, germLoopPath_pos,
            uLiftPath_append _ _ _ a hp, pathChain_append,
            extendList_loopCoefficientVertex N p ψ hψ, map_add, ih]
          simp only [↓reduceIte, loopCoefficientChainMap,
            Finsupp.linearCombination_single, one_smul]
      | false =>
          have hp : IsPath X.src X.tgt (revPath (p i).1)
              (endV (loopCoefficientVertex N ψ g)) a := by
            rw [loopCoefficientVertex_end]
            exact isPath_revPath (p i).2
          rw [liftPath_cons_false, pathChain_cons, wordPath_cons, germLoopPath_neg,
            uLiftPath_append _ _ _ a hp, pathChain_append,
            extendList_rev_loopCoefficientVertex N p ψ hψ, map_add, ih,
            lifted_loop_reverse_chain N p ψ hψ]
          simp only [Bool.false_eq_true, ↓reduceIte, map_neg,
            loopCoefficientChainMap, Finsupp.linearCombination_single, one_smul]

variable [Fintype I] [DecidableEq I]

include hψ in
/-- The full coefficient vector is the projected Fox gradient of the word;
the result keeps each individual translated generator-loop chain. -/
theorem lifted_wordPath_fox (l : List (I × Bool)) :
    pathChain (uLiftPath (wordPath p l) (UV.base X a)) =
      loopCoefficientChainMap N p ψ
        ((coords N I).symm (fun i => proj N (fox i (FreeGroup.mk l)))) := by
  have hcoords : coords N I (pathChain (liftPath (Nsub := N) l 1)) =
      fun i => proj N (fox i (FreeGroup.mk l)) := by
    simpa only [show (MonoidAlgebra.single (1 : FreeGroup I ⧸ N) (1 : ℤ)) = 1 from rfl,
      one_mul] using coords_pathChain_liftPath (Nsub := N) l (1 : FreeGroup I ⧸ N)
  have hc := congrArg (coords N I).symm hcoords
  rw [LinearEquiv.symm_apply_apply] at hc
  rw [← hc, loopCoefficientChainMap_liftPath N p ψ hψ]
  simp only [loopCoefficientVertex, map_one, deckV_one]

end FiniteChains.Comb
