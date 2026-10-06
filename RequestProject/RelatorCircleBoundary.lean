module

public import RequestProject.RelatorCircleEdges

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

theorem relatorCircle_boundary_left
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ) (k : Fin (w j).length) :
    (Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c)
      (relatorCirclePoint w j k CPos.cedgL) =
        c (relatorCircleEdge0 w j k) + c (relatorCircleEdge1 w j k) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single e n =>
    obtain ⟨l, he⟩ := relatorCircle_edge_cases w j e
    rcases he with rfl | rfl | rfl | rfl <;>
      simp [Comb.bdry1, strictOrderCx, relatorCircleEdge0, relatorCircleEdge1,
        relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt,
        Finsupp.single_apply, RelatorCircle, StrictOrdEdge, TCirc]

theorem relatorCircle_boundary_mid
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ) (k : Fin (w j).length) :
    (Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c)
      (relatorCirclePoint w j k CPos.cmid) =
        -c (relatorCircleEdge1 w j k) - c (relatorCircleEdge2 w j k) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single e n =>
    obtain ⟨l, he⟩ := relatorCircle_edge_cases w j e
    rcases he with rfl | rfl | rfl | rfl <;>
      simp [Comb.bdry1, strictOrderCx, relatorCircleEdge0, relatorCircleEdge1,
        relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt,
        Finsupp.single_apply, RelatorCircle, StrictOrdEdge, TCirc]

theorem relatorCircle_boundary_right
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ) (k : Fin (w j).length) :
    (Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c)
      (relatorCirclePoint w j k CPos.cedgR) =
        c (relatorCircleEdge2 w j k) + c (relatorCircleEdge3 w j k) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single e n =>
    obtain ⟨l, he⟩ := relatorCircle_edge_cases w j e
    rcases he with rfl | rfl | rfl | rfl <;>
      simp [Comb.bdry1, strictOrderCx, relatorCircleEdge0, relatorCircleEdge1,
        relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt,
        Finsupp.single_apply, RelatorCircle, StrictOrdEdge, TCirc]
    all_goals
      by_cases h : l = k
      · subst l
        simp
      · have hv : l.val ≠ k.val := fun he => h (Fin.ext he)
        simp [hv]

theorem relatorCircleNext_injective : Function.Injective (relatorCircleNext w j) := by
  intro k l he
  have he' := congrArg Fin.val he
  change (k.val + 1) % (w j).length = (l.val + 1) % (w j).length at he'
  have hk := k.isLt
  have hl := l.isLt
  apply Fin.ext
  by_cases hks : k.val + 1 < (w j).length <;>
    by_cases hls : l.val + 1 < (w j).length
  · rw [Nat.mod_eq_of_lt hks, Nat.mod_eq_of_lt hls] at he'
    omega
  · have hs : l.val + 1 = (w j).length := by omega
    rw [Nat.mod_eq_of_lt hks, hs, Nat.mod_self] at he'
    omega
  · have hs : k.val + 1 = (w j).length := by omega
    rw [hs, Nat.mod_self, Nat.mod_eq_of_lt hls] at he'
    omega
  · omega

theorem relatorCircle_boundary_corner
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ) (k : Fin (w j).length) :
    (Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c)
      (relatorCirclePoint w j (relatorCircleNext w j k) CPos.cor) =
        -c (relatorCircleEdge0 w j (relatorCircleNext w j k)) -
          c (relatorCircleEdge3 w j k) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single e n =>
    obtain ⟨l, he⟩ := relatorCircle_edge_cases w j e
    rcases he with rfl | rfl | rfl | rfl <;>
      simp [Comb.bdry1, strictOrderCx, relatorCircleEdge0, relatorCircleEdge1,
        relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt,
        Finsupp.single_apply, RelatorCircle, StrictOrdEdge, TCirc]
    by_cases h : l = k
    · subst l
      simp
    · have hn : (relatorCircleNext w j l).val ≠ (relatorCircleNext w j k).val := by
        intro he
        exact h (relatorCircleNext_injective w j (Fin.ext he))
      simp [hn]

theorem relatorCircle_cycle_coefficients
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c = 0)
    (k : Fin (w j).length) :
    c (relatorCircleEdge1 w j k) = -c (relatorCircleEdge0 w j k) ∧
    c (relatorCircleEdge2 w j k) = c (relatorCircleEdge0 w j k) ∧
    c (relatorCircleEdge3 w j k) = -c (relatorCircleEdge0 w j k) ∧
    c (relatorCircleEdge0 w j (relatorCircleNext w j k)) =
      c (relatorCircleEdge0 w j k) := by
  have hl := relatorCircle_boundary_left w j c k
  have hm := relatorCircle_boundary_mid w j c k
  have hr := relatorCircle_boundary_right w j c k
  have hk := relatorCircle_boundary_corner w j c k
  rw [hc, Finsupp.zero_apply] at hl hm hr hk
  omega

theorem relatorCircle_successor_invariant_constant
    (a : Fin (w j).length → ℤ)
    (ha : ∀ k, a (relatorCircleNext w j k) = a k)
    (hpos : 0 < (w j).length) (k : Fin (w j).length) :
    a k = a ⟨0, hpos⟩ := by
  have hi : ∀ n (hn : n < (w j).length), a ⟨n, hn⟩ = a ⟨0, hpos⟩ := by
    intro n
    induction n with
    | zero => intro hn; rfl
    | succ n ih =>
      intro hn
      have hp : n < (w j).length := by omega
      have hs : relatorCircleNext w j ⟨n, hp⟩ = ⟨n + 1, hn⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hn
      rw [← hs, ha]
      exact ih hp
  exact hi k.val k.isLt

theorem relatorCircle_cycle_coefficient_constant
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c = 0)
    (hpos : 0 < (w j).length) (k : Fin (w j).length) :
    c (relatorCircleEdge0 w j k) = c (relatorCircleEdge0 w j ⟨0, hpos⟩) := by
  apply relatorCircle_successor_invariant_constant w j
    (fun l => c (relatorCircleEdge0 w j l)) _ hpos k
  intro l
  exact (relatorCircle_cycle_coefficients w j c hc l).2.2.2

theorem relatorCircle_cycle_all_coefficients
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c = 0)
    (hpos : 0 < (w j).length) (k : Fin (w j).length) :
    let a := c (relatorCircleEdge0 w j ⟨0, hpos⟩)
    c (relatorCircleEdge0 w j k) = a ∧
    c (relatorCircleEdge1 w j k) = -a ∧
    c (relatorCircleEdge2 w j k) = a ∧
    c (relatorCircleEdge3 w j k) = -a := by
  dsimp only
  have h := relatorCircle_cycle_coefficients w j c hc k
  have h0 := relatorCircle_cycle_coefficient_constant w j c hc hpos k
  exact ⟨h0, h.1.trans (congrArg Neg.neg h0), h.2.1.trans h0,
    h.2.2.1.trans (congrArg Neg.neg h0)⟩

/-- Agreement at one genuine circle edge determines an entire one-cycle. -/
theorem relatorCircle_cycle_ext
    (c d : StrictOrdEdge (RelatorCircle w j) →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c = 0)
    (hd : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) d = 0)
    (hpos : 0 < (w j).length)
    (he : c (relatorCircleEdge0 w j ⟨0, hpos⟩) =
      d (relatorCircleEdge0 w j ⟨0, hpos⟩)) : c = d := by
  ext e
  obtain ⟨k, hk⟩ := relatorCircle_edge_cases w j e
  have hck := relatorCircle_cycle_all_coefficients w j c hc hpos k
  have hdk := relatorCircle_cycle_all_coefficients w j d hd hpos k
  dsimp only at hck hdk
  rcases hk with rfl | rfl | rfl | rfl
  · exact hck.1.trans (he.trans hdk.1.symm)
  · exact hck.2.1.trans ((congrArg Neg.neg he).trans hdk.2.1.symm)
  · exact hck.2.2.1.trans (he.trans hdk.2.2.1.symm)
  · exact hck.2.2.2.trans ((congrArg Neg.neg he).trans hdk.2.2.2.symm)

/-- An empty attaching word has no actual valid strict circle edges. -/
theorem relatorCircle_chain_zero_of_length_zero
    (hzero : (w j).length = 0) (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ) :
    c = 0 := by
  ext e
  obtain ⟨k, _⟩ := relatorCircle_edge_cases w j e
  have hk := k.isLt
  omega

end FiniteChains.PresModel
