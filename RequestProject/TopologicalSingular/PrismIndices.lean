module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.SingularChainMaps

@[expose] public section

/-! # Vertex maps for the standard triangulation of a prism -/


namespace FiniteChains.SingularPrism

open CategoryTheory

def cut (i : ℕ) {m : ℕ} (j : Fin m) : Fin 2 := if j.val ≤ i then 0 else 1

theorem cut_left {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) (h : j ≤ i.castSucc) :
    cut i.succ.val ∘ j.castSucc.succAbove = (cut i.val : Fin (n + 2) → Fin 2) := by
  funext k
  have hh : j.val ≤ i.val := h
  simp only [Function.comp_apply, cut, Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
    Fin.val_succ]
  split_ifs <;> simp_all only [Fin.val_castSucc, Fin.val_succ] <;> first | rfl | omega

theorem cut_right {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) (h : i.castSucc < j) :
    cut i.castSucc.val ∘ j.succ.succAbove = (cut i.val : Fin (n + 2) → Fin 2) := by
  funext k
  have hh : i.val < j.val := h
  have hv : (j.succ.succAbove k).val = if k.val < j.val + 1 then k.val else k.val + 1 := by
    by_cases hk : k.val < j.val + 1
    · rw [Fin.succAbove_of_castSucc_lt _ _ hk, if_pos hk]
      rfl
    · rw [Fin.succAbove_of_le_castSucc _ _ (show j.succ ≤ k.castSucc from Nat.le_of_not_gt hk), if_neg hk]
      rfl
  have he : (j.succ.succAbove k).val ≤ i.val ↔ k.val ≤ i.val := by
    rw [hv]
    split_ifs <;> omega
  simp only [Function.comp_apply, cut, Fin.val_castSucc, he]

theorem cut_middle {n : ℕ} (i : Fin n) :
    cut i.succ.val ∘ i.succ.castSucc.succAbove =
      (cut i.castSucc.val ∘ i.succ.castSucc.succAbove : Fin (n + 1) → Fin 2) := by
  funext k
  simp only [Function.comp_apply, cut, Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
    Fin.val_succ]
  split_ifs <;> simp_all only [Fin.val_castSucc, Fin.val_succ] <;> first | rfl | omega

theorem cut_first (n : ℕ) :
    cut 0 ∘ (0 : Fin (n + 2)).succAbove = (fun _ : Fin (n + 1) => (1 : Fin 2)) := by
  funext k
  simp only [Function.comp_apply, Fin.succAbove_zero, cut, Fin.val_succ]
  simp

theorem cut_last (n : ℕ) :
    cut n ∘ (Fin.last (n + 1)).succAbove = (fun _ : Fin (n + 1) => (0 : Fin 2)) := by
  funext k
  simp only [Function.comp_apply, Fin.succAbove_last, cut, Fin.val_castSucc]
  exact if_pos (Nat.le_of_lt_succ k.isLt)

theorem base_left {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) (h : j ≤ i.castSucc) :
    i.succ.predAbove ∘ j.castSucc.succAbove = j.succAbove ∘ i.predAbove := by
  funext k
  exact congrArg (fun f : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk (n + 1) => f k)
    (SimplexCategory.δ_comp_σ_of_le h)

theorem base_right {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) (h : i.castSucc < j) :
    i.castSucc.predAbove ∘ j.succ.succAbove = j.succAbove ∘ i.predAbove := by
  funext k
  exact congrArg (fun f : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk (n + 1) => f k)
    (SimplexCategory.δ_comp_σ_of_gt h)

theorem base_same {n : ℕ} (i : Fin (n + 1)) :
    i.predAbove ∘ i.castSucc.succAbove = id := by
  funext k
  exact Fin.predAbove_succAbove i k

theorem base_next {n : ℕ} (i : Fin (n + 1)) :
    i.predAbove ∘ i.succ.succAbove = id := by
  funext k
  exact congrArg (fun f : SimplexCategory.mk n ⟶ SimplexCategory.mk n => f k)
    (SimplexCategory.δ_comp_σ_succ (i := i))

end FiniteChains.SingularPrism
