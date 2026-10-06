/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.PrismIndices

/-! # Continuous prism simplices and all their face identities -/


set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.SingularPrism

open Set Topology TopologicalSingular

theorem stdMap_const {m n : ℕ} (b : Fin n) (z : stdSimplex ℝ (Fin m)) :
    stdSimplex.map (fun _ : Fin m => b) z = stdSimplex.vertex b := by
  classical
  apply Subtype.ext
  funext j
  simp only [stdSimplex.map, FunOnFinite.linearMap_apply_apply]
  by_cases h : b = j
  · subst j
    simp
  · simp [h]

noncomputable def prismMap {n : ℕ} (i : Fin (n + 1)) : C(Domain (n + 1), unitInterval × Domain n) :=
  ⟨fun z => (stdSimplexHomeomorphUnitInterval (stdSimplex.map (cut i.val) z),
      stdSimplex.map i.predAbove z),
    (stdSimplexHomeomorphUnitInterval.continuous.comp (stdSimplex.continuous_map _)).prodMk
      (stdSimplex.continuous_map _)⟩

theorem prismMap_left {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) (h : j ≤ i.castSucc)
    (z : Domain (n + 1)) :
    prismMap i.succ (stdSimplex.map j.castSucc.succAbove z) =
      ((prismMap i z).1, stdSimplex.map j.succAbove (prismMap i z).2) := by
  simp only [prismMap, ContinuousMap.coe_mk, stdSimplex.map_comp_apply]
  rw [cut_left i j h, base_left i j h]

theorem prismMap_right {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) (h : i.castSucc < j)
    (z : Domain (n + 1)) :
    prismMap i.castSucc (stdSimplex.map j.succ.succAbove z) =
      ((prismMap i z).1, stdSimplex.map j.succAbove (prismMap i z).2) := by
  simp only [prismMap, ContinuousMap.coe_mk, stdSimplex.map_comp_apply]
  rw [cut_right i j h, base_right i j h]

theorem prismMap_middle {n : ℕ} (i : Fin n) (z : Domain n) :
    prismMap i.castSucc (stdSimplex.map i.succ.castSucc.succAbove z) =
      prismMap i.succ (stdSimplex.map i.succ.castSucc.succAbove z) := by
  apply Prod.ext
  · simp only [prismMap, ContinuousMap.coe_mk, stdSimplex.map_comp_apply]
    rw [cut_middle]
  · change stdSimplex.map i.castSucc.predAbove (stdSimplex.map i.succ.castSucc.succAbove z) =
      stdSimplex.map i.succ.predAbove (stdSimplex.map i.succ.castSucc.succAbove z)
    rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
    change stdSimplex.map (i.castSucc.predAbove ∘ i.castSucc.succ.succAbove) z =
      stdSimplex.map (i.succ.predAbove ∘ i.succ.castSucc.succAbove) z
    rw [base_next, base_same]

theorem prismMap_first (n : ℕ) (z : Domain n) :
    prismMap (0 : Fin (n + 1)) (stdSimplex.map (0 : Fin (n + 2)).succAbove z) = (1, z) := by
  apply Prod.ext
  · change stdSimplexHomeomorphUnitInterval
      (stdSimplex.map (cut 0) (stdSimplex.map (0 : Fin (n + 2)).succAbove z)) = 1
    rw [stdSimplex.map_comp_apply, cut_first, stdMap_const]
    exact stdSimplexHomeomorphUnitInterval_one
  · change stdSimplex.map (0 : Fin (n + 1)).predAbove
      (stdSimplex.map (0 : Fin (n + 2)).succAbove z) = z
    rw [stdSimplex.map_comp_apply]
    change stdSimplex.map ((0 : Fin (n + 1)).predAbove ∘ (0 : Fin (n + 1)).castSucc.succAbove) z = z
    rw [base_same, stdSimplex.map_id_apply]

theorem prismMap_last (n : ℕ) (z : Domain n) :
    prismMap (Fin.last n) (stdSimplex.map (Fin.last (n + 1)).succAbove z) = (0, z) := by
  apply Prod.ext
  · change stdSimplexHomeomorphUnitInterval
      (stdSimplex.map (cut n) (stdSimplex.map (Fin.last (n + 1)).succAbove z)) = 0
    rw [stdSimplex.map_comp_apply, cut_last, stdMap_const]
    exact stdSimplexHomeomorphUnitInterval_zero
  · change stdSimplex.map (Fin.last n).predAbove
      (stdSimplex.map (Fin.last (n + 1)).succAbove z) = z
    rw [stdSimplex.map_comp_apply]
    change stdSimplex.map ((Fin.last n).predAbove ∘ (Fin.last n).succ.succAbove) z = z
    rw [base_next, stdSimplex.map_id_apply]

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)

noncomputable def simplex {n : ℕ} (σ : Simplex X n) (i : Fin (n + 1)) : Simplex Y (n + 1) :=
  H.toContinuousMap.comp ⟨fun z => ((prismMap i z).1, σ (prismMap i z).2),
    (prismMap i).continuous.fst.prodMk (σ.continuous.comp (prismMap i).continuous.snd)⟩

theorem simplex_left {n : ℕ} (σ : Simplex X (n + 1)) (i : Fin (n + 1)) (j : Fin (n + 2))
    (h : j ≤ i.castSucc) :
    face j.castSucc (simplex H σ i.succ) = simplex H (face j σ) i := by
  apply ContinuousMap.ext
  intro z
  change H ((prismMap i.succ (stdSimplex.map j.castSucc.succAbove z)).1,
      σ (prismMap i.succ (stdSimplex.map j.castSucc.succAbove z)).2) = _
  rw [prismMap_left i j h]
  rfl

theorem simplex_right {n : ℕ} (σ : Simplex X (n + 1)) (i : Fin (n + 1)) (j : Fin (n + 2))
    (h : i.castSucc < j) :
    face j.succ (simplex H σ i.castSucc) = simplex H (face j σ) i := by
  apply ContinuousMap.ext
  intro z
  change H ((prismMap i.castSucc (stdSimplex.map j.succ.succAbove z)).1,
      σ (prismMap i.castSucc (stdSimplex.map j.succ.succAbove z)).2) = _
  rw [prismMap_right i j h]
  rfl

theorem simplex_middle {n : ℕ} (σ : Simplex X n) (i : Fin n) :
    face i.succ.castSucc (simplex H σ i.castSucc) = face i.succ.castSucc (simplex H σ i.succ) := by
  apply ContinuousMap.ext
  intro z
  change H ((prismMap i.castSucc (stdSimplex.map i.succ.castSucc.succAbove z)).1,
      σ (prismMap i.castSucc (stdSimplex.map i.succ.castSucc.succAbove z)).2) = _
  rw [prismMap_middle]
  rfl

theorem simplex_first (n : ℕ) (σ : Simplex X n) :
    face 0 (simplex H σ 0) = simplexMap g n σ := by
  apply ContinuousMap.ext
  intro z
  change H ((prismMap (0 : Fin (n + 1)) (stdSimplex.map (0 : Fin (n + 2)).succAbove z)).1,
      σ (prismMap (0 : Fin (n + 1)) (stdSimplex.map (0 : Fin (n + 2)).succAbove z)).2) = _
  rw [prismMap_first]
  exact H.apply_one _

theorem simplex_last (n : ℕ) (σ : Simplex X n) :
    face (Fin.last (n + 1)) (simplex H σ (Fin.last n)) = simplexMap f n σ := by
  apply ContinuousMap.ext
  intro z
  change H ((prismMap (Fin.last n) (stdSimplex.map (Fin.last (n + 1)).succAbove z)).1,
      σ (prismMap (Fin.last n) (stdSimplex.map (Fin.last (n + 1)).succAbove z)).2) = _
  rw [prismMap_last]
  exact H.apply_zero _

end FiniteChains.SingularPrism
